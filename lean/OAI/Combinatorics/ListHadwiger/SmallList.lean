import OAI.Combinatorics.ListHadwiger.StageSampling

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset Filter

noncomputable def rate (t : ℝ) (j : ℕ) : ℝ := 4*t/(2:ℝ)^j
noncomputable def bins (t : ℝ) (j : ℕ) : ℕ :=
  ⌈192*rate t j*Real.log (2*max 1 (t/rate t j))⌉₊

lemma rate_pos {t : ℝ} (ht : 0 < t) (j : ℕ) : 0 < rate t j := by
  unfold rate
  positivity

lemma rate_zero (t : ℝ) : rate t 0=4*t := by simp [rate]
lemma rate_succ (t : ℝ) (j : ℕ) : rate t (j+1)=rate t j/2 := by
  simp only [rate,pow_succ]
  ring

lemma rate_le {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : rate t j ≤ 4*t := by
  exact div_le_self (by positivity) (one_le_pow₀ (by norm_num))

lemma geometric_budget (m : ℕ) :
    ∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j ≤ 4 := by
  have he : (∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+2*((m:ℝ)+2)/(2:ℝ)^m=4 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [sum_range_succ]
      push_cast
      rw [pow_succ]
      calc
        _ = (∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+2*((m:ℝ)+2)/(2:ℝ)^m := by ring
        _ = 4 := ih
  have : 0 ≤ 2*((m:ℝ)+2)/(2:ℝ)^m := by positivity
  linarith

lemma bins_upper {t : ℝ} (ht : 0 < t) (j : ℕ) :
    (bins t j : ℝ) ≤ 768*t*(((j:ℝ)+1)/(2:ℝ)^j)+1 := by
  have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have he : t/rate t j=(2:ℝ)^j/4 := by unfold rate; field_simp
  have hy : max 1 (t/rate t j) ≤ (2:ℝ)^j := by rw [he]; exact max_le hp (by linarith)
  have hy0 : 0 < 2*max 1 (t/rate t j) := by have := le_max_left 1 (t/rate t j); linarith
  have hl : Real.log (2*max 1 (t/rate t j)) ≤ (j:ℝ)+1 := by
    calc
      _ ≤ Real.log ((2:ℝ)^(j+1)) := Real.log_le_log hy0 (by rw [pow_succ]; nlinarith)
      _ = ((j:ℝ)+1)*Real.log 2 := by rw [Real.log_pow]; push_cast; rfl
      _ ≤ _ := by nlinarith [Real.log_two_lt_d9]
  have hnonneg : 0 ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j)) := by
    have hh : 1 ≤ 2*max 1 (t/rate t j) := by have := le_max_left 1 (t/rate t j); linarith
    exact mul_nonneg (by positivity [rate_pos ht j]) (Real.log_nonneg hh)
  have hb := (Nat.ceil_lt_add_one hnonneg).le
  change (bins t j:ℝ) ≤ _ at hb
  calc
    _ ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j))+1 := hb
    _ ≤ 192*rate t j*((j:ℝ)+1)+1 := by gcongr; have := rate_pos ht j; positivity
    _ = _ := by unfold rate; ring

lemma bins_lower {t : ℝ} (ht : 1 < t) (j : ℕ)
    (hr : t/Real.log t ≤ rate t j) : t/Real.log t ≤ (bins t j:ℝ) := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := Real.log_pos ht
  have hlog : Real.log 2 ≤ Real.log (2*max 1 (t/rate t j)) :=
    Real.log_le_log (by norm_num) (by have := le_max_left 1 (t/rate t j); linarith)
  have hlg : 1 ≤ 192*Real.log (2*max 1 (t/rate t j)) := by linarith [Real.log_two_gt_d9]
  calc
    _ ≤ rate t j := hr
    _ ≤ 192*rate t j*Real.log (2*max 1 (t/rate t j)) := by nlinarith [rate_pos ht0 j]
    _ ≤ (bins t j:ℝ) := Nat.le_ceil _

lemma power_two_lower (m : ℕ) : (m:ℝ)+1 ≤ (2:ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [pow_succ]; push_cast; nlinarith

theorem schedule_cutoff : ∀ᶠ t : ℝ in atTop,
    1 < t ∧ 1 ≤ Real.log t ∧ 4*Real.log t ≤ t ∧
    t^(7/10:ℝ) ≤ t/Real.log t := by
  have hl := (Real.isLittleO_log_id_atTop).bound (show (0:ℝ)<1/4 by norm_num)
  have hp := (isLittleO_log_rpow_rpow_atTop (1:ℝ)
    (show (0:ℝ)<3/10 by norm_num)).bound (show (0:ℝ)<1 by norm_num)
  have hg := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hl,hp,hg] with t ht hl hp hg
  have ht0 : 0<t := by linarith
  have hg0 : 0<Real.log t := by linarith
  have hl' : Real.log t ≤ (1/4:ℝ)*t := by
    simpa only [id_eq,Real.norm_eq_abs,abs_of_pos hg0,abs_of_pos ht0] using hl
  have hp' : Real.log t ≤ t^(3/10:ℝ) := by
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos hg0,
      abs_of_nonneg (Real.rpow_nonneg ht0.le (3/10:ℝ)),one_mul] using hp
  refine ⟨ht,hg,by linarith,?_⟩
  apply (le_div_iff₀ hg0).mpr
  calc
    _ ≤ t^(7/10:ℝ)*t^(3/10:ℝ) := mul_le_mul_of_nonneg_left hp' (by positivity)
    _ = t := by rw [←Real.rpow_add ht0]; norm_num

theorem schedule_exists (t : ℕ) (ht : 1 < (t:ℝ))
    (hl : 1 ≤ Real.log t) (hlog : 4*Real.log t ≤ t)
    (hp : (t:ℝ)^(7/10:ℝ) ≤ (t:ℝ)/Real.log t) :
    ∃ m : ℕ, m ≤ t ∧ rate t m < (t:ℝ)/Real.log t ∧
      (∀ j < m, (t:ℝ)/Real.log t ≤ rate t j ∧ rate t j ≤ 4*t) ∧
      (∑ j ∈ range m, bins t j)+16*t ≤ 4096*t ∧
      (∀ j < m, (t:ℝ)^(7/10:ℝ) ≤ (bins t j:ℝ)) ∧
      (t:ℝ)^(7/10:ℝ) ≤ 16*t := by
  have ht0 : 0 < (t:ℝ) := by linarith
  have hl0 : 0 < Real.log t := by linarith
  have hlast : rate t t < (t:ℝ)/Real.log t := by
    dsimp [rate]
    apply (div_lt_div_iff₀ (by positivity) hl0).mpr
    have hh := power_two_lower t
    nlinarith
  let m := Nat.find (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩)
  have hm : m ≤ t := Nat.find_min' _ hlast
  have hterm : rate t m < (t:ℝ)/Real.log t :=
    Nat.find_spec (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩)
  have hvalid : ∀ j < m, (t:ℝ)/Real.log t ≤ rate t j := by
    intro j hj
    exact le_of_not_gt (Nat.find_min (show ∃ m, rate t m < (t:ℝ)/Real.log t from ⟨t,hlast⟩) hj)
  refine ⟨m,hm,hterm,fun j hj => ⟨hvalid j hj,rate_le ht0.le j⟩,?_,?_,?_⟩
  · apply (Nat.cast_le (α := ℝ)).mp
    push_cast
    have hs : (∑ j ∈ range m, (bins t j:ℝ)) ≤ 3072*t+(m:ℝ) := by
      calc
        _ ≤ ∑ j ∈ range m, (768*(t:ℝ)*(((j:ℝ)+1)/(2:ℝ)^j)+1) :=
          sum_le_sum fun j _ => bins_upper ht0 j
        _ = 768*(t:ℝ)*(∑ j ∈ range m, ((j:ℝ)+1)/(2:ℝ)^j)+(m:ℝ) := by
          rw [sum_add_distrib,←mul_sum]; simp
        _ ≤ _ := by have := geometric_budget m; nlinarith
    have hm' : (m:ℝ) ≤ t := by exact_mod_cast hm
    nlinarith
  · exact fun j hj => hp.trans (bins_lower ht j (hvalid j hj))
  · exact hp.trans ((div_le_self ht0.le hl).trans (by nlinarith))

theorem palette_tail_cutoff : ∀ᶠ t : ℝ in atTop,
    ∀ (n b j : ℕ) (u : Fin j → ℕ), n ≤ t^(11/10:ℝ) → 1 ≤ b →
      (b:ℝ) ≤ 4096*t → (j:ℝ) ≤ t+1 →
      (∀ i, t^(7/10:ℝ) ≤ (u i:ℝ)) →
      (n:ℝ)*(∑ i, (2:ℝ)^(u i)*Real.exp (-(32768*t)*(u i)/(2*b))) < 1 := by
  have hh := Sampling.polynomial_tail_cutoff 1 (21/10) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hh] with t ht hh
  intro n b j u hn hb hb' hj hu
  have ht0 : 0<t := by linarith
  have hb0 : 0 < (b:ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hratio : 4 ≤ (32768*t)/(2*b) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hterm (i : Fin j) : (2:ℝ)^(u i)*Real.exp (-(32768*t)*(u i)/(2*b)) ≤
      Real.exp (-t^(7/10:ℝ)) := by
    have he : (2:ℝ)^(u i)=Real.exp ((u i:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [he,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he' : -(32768*t)*(u i)/(2*b)= -((32768*t)/(2*b))*(u i) := by ring
    rw [he']
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hmul := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg (u i))
    have hmul' := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (u i))
    nlinarith [hu i]
  calc
    _ ≤ (n:ℝ)*(∑ _i : Fin j, Real.exp (-t^(7/10:ℝ))) := by gcongr with i; exact hterm i
    _ = (n:ℝ)*((j:ℝ)*Real.exp (-t^(7/10:ℝ))) := by simp [nsmul_eq_mul]
    _ ≤ t^(11/10:ℝ)*((2*t)*Real.exp (-t^(7/10:ℝ))) := by gcongr; linarith
    _ = 1*t^(21/10:ℝ)*(2*Real.exp (-t^(7/10:ℝ))) := by
      have he : t^(11/10:ℝ)*t=t^(21/10:ℝ) := by
        calc
          _ = t^(11/10:ℝ)*t^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [←Real.rpow_add ht0]; norm_num
      rw [show t^(11/10:ℝ)*((2*t)*Real.exp (-t^(7/10:ℝ))) =
        2*(t^(11/10:ℝ)*t)*Real.exp (-t^(7/10:ℝ)) by ring,he]
      ring
    _ < 1 := hh

end LinearListHadwiger.SmallList

namespace LinearListHadwiger.SmallList
open Finset Fractional
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FractionalObstruction (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, 4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) <
    number (G.induce (↑S:Set V))

noncomputable def singletonModel {W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W → V) (hf : Function.Injective f)
    (ha : ∀ ⦃u v⦄, H.Adj u v → G.Adj (f u) (f v)) : MinorModel G H where
  branch w := {f w}
  connected w := by
    have : Nonempty ({f w}:Set V) := ⟨⟨f w,rfl⟩⟩
    exact SimpleGraph.Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr (fun he => hn (hf he))
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,ha h⟩

lemma number_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : number G=number H := by
  apply le_antisymm
  · have he : G=H.comap e := by ext u v; exact e.map_adj_iff.symm
    rw [he]
    exact number_comap H e
  · have he : H=G.comap e.symm := by ext u v; exact e.symm.map_adj_iff.symm
    rw [he]
    exact number_comap G e.symm

noncomputable def induceImageIso (G : SimpleGraph V) (R : Finset V)
    (A : Finset (↑R:Set V)) :
    (G.induce (↑R:Set V)).induce (↑A:Set (↑R:Set V)) ≃g
      G.induce (↑(A.image Subtype.val):Set V) where
  toFun a := ⟨a.val.val,mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  invFun v := ⟨⟨v.val,by obtain ⟨a,_,he⟩ := mem_image.mp v.property; exact he ▸ a.property⟩,
    by
      obtain ⟨a,ha,he⟩ := mem_image.mp v.property
      have ha' : a=⟨v.val,by exact he ▸ a.property⟩ := Subtype.ext he
      change (⟨v.val,_⟩ : (↑R:Set V)) ∈ A
      simpa only [ha'] using ha⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := rfl
  map_rel_iff' := by intros; rfl

omit [Fintype V] in
lemma obstruction_induce (G : SimpleGraph V) (R : Finset V)
    (h : FractionalObstruction (G.induce (↑R:Set V))) : FractionalObstruction G := by
  obtain ⟨A,hA⟩ := h
  let e := induceImageIso G R A
  have hm := (singletonModel _ _ e.symm e.symm.injective
    (fun {_ _} ha => e.symm.map_adj_iff.mpr ha)).hadwiger_le
  refine ⟨A.image Subtype.val,?_⟩
  rw [number_iso e] at hA
  have hm' : (hadwigerNumber (G.induce (↑(A.image Subtype.val):Set V)):ℝ) ≤
      hadwigerNumber ((G.induce (↑R:Set V)).induce (↑A:Set (↑R:Set V))) := by
    exact_mod_cast hm
  linarith

lemma number_le_four (G : SimpleGraph V) (h : ¬FractionalObstruction G) :
    number G ≤ 4*(hadwigerNumber G:ℝ) := by
  have hh : number (G.induce (↑(univ:Finset V):Set V)) ≤
      4*(hadwigerNumber (G.induce (↑(univ:Finset V):Set V)):ℝ) :=
    le_of_not_gt (fun hn => h ⟨univ,hn⟩)
  have he : G=(G.induce (↑(univ:Finset V):Set V)).comap
      (fun v => ⟨v,mem_univ v⟩) := rfl
  have hn : number G ≤ number (G.induce (↑(univ:Finset V):Set V)) := by
    rw [he]
    exact number_comap _ _
  have hm := (Knitting.model_induce G univ).hadwiger_le
  have hm' : (hadwigerNumber (G.induce (↑(univ:Finset V):Set V)):ℝ) ≤ hadwigerNumber G := by
    exact_mod_cast hm
  linarith

omit [Fintype V] in
lemma stable_image {G : SimpleGraph V} {R : Finset V} {A : Finset (↑R:Set V)}
    (h : Stable (G.induce (↑R:Set V)) A) : Stable G (A.image Subtype.val) := by
  intro u hu v hv hav
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  exact h a ha b hb hav

section Palette
variable {J Color : Type} [Fintype J] [DecidableEq J]
variable (u : J → ℕ)

abbrev Palette := (j : J) × Fin (u j)

noncomputable def block (j : J) : Finset (Palette u) :=
  univ.map (Function.Embedding.sigmaMk j)

omit [Fintype J] [DecidableEq J] in
lemma block_card (j : J) : (block u j).card=u j := by simp [block]

omit [Fintype J] [DecidableEq J] in
lemma mem_block (b : Palette u) (j : J) : b∈block u j ↔ b.1=j := by
  simp only [block,mem_map,mem_univ,true_and,Function.Embedding.sigmaMk_apply]
  constructor
  · rintro ⟨a,rfl⟩; rfl
  · intro hb; subst j; exact ⟨b.2,rfl⟩

noncomputable def eligible (L : V → Finset Color) (f : Color → Palette u)
    (j : J) (b : Fin (u j)) : Finset V := univ.filter (fun v => ∃ c∈L v, f c=⟨j,b⟩)

omit [Fintype J] in
lemma occupied_card (L : V → Finset Color) (f : Color → Palette u) (v : V) (j : J) :
    (ColorBins.occupied (L v) (block u j) f).card=
      (univ.filter (fun b : Fin (u j) => v∈eligible u L f j b)).card := by
  classical
  have he : ColorBins.occupied (L v) (block u j) f =
      (univ.filter (fun b : Fin (u j) => v∈eligible u L f j b)).map
        (Function.Embedding.sigmaMk j) := by
    ext b
    simp only [ColorBins.occupied,mem_inter,mem_image,mem_map,mem_filter,mem_univ,
      true_and,eligible,Function.Embedding.sigmaMk_apply]
    constructor
    · rintro ⟨hb,⟨c,hc,he⟩⟩
      have hb' := (mem_block u b j).mp hb
      subst j
      exact ⟨b.2,⟨c,hc,he⟩,rfl⟩
    · rintro ⟨a,⟨c,hc,he⟩,rfl⟩
      exact ⟨(mem_block u ⟨j,a⟩ j).mpr rfl,⟨c,hc,he⟩⟩
  rw [he,card_map]

end Palette

noncomputable def blockSize (t m : ℕ) (j : Fin (m+1)) : ℕ :=
  if j.val < m then bins t j.val else 16*t

lemma blockSize_stage (t m : ℕ) (j : Fin m) :
    blockSize t m j.castSucc=bins t j.val := by simp [blockSize,j.isLt]

lemma blockSize_cleanup (t m : ℕ) : blockSize t m (Fin.last m)=16*t := by
  simp [blockSize]

lemma palette_card (t m : ℕ) :
    Fintype.card (Palette (blockSize t m))=(∑ j∈range m,bins t j)+16*t := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_castSucc]
  simp only [blockSize_stage,blockSize_cleanup]
  rw [Fin.sum_univ_eq_sum_range]

abbrev RunPalette (t m : ℕ) := ((j : Fin m) × Fin (bins t j.val)) ⊕ Fin (16*t)

def stageBin (t m : ℕ) (j : Fin m) (b : Fin (bins t j.val)) : RunPalette t m :=
  Sum.inl ⟨j,b⟩

def binIndex {t m : ℕ} : RunPalette t m → ℕ :=
  Sum.elim (fun b => b.1.val) (fun _ => m)

lemma stageBin_injective (t m : ℕ) (j : Fin m) :
    Function.Injective (stageBin t m j) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2

noncomputable def runBlock (t m : ℕ) : Option (Fin m) → Finset (RunPalette t m)
  | none => univ.map Function.Embedding.inr
  | some j => univ.map ⟨stageBin t m j,stageBin_injective t m j⟩

lemma runBlock_none (t m : ℕ) : (runBlock t m none).card=16*t := by
  simp [runBlock]

lemma runBlock_some (t m : ℕ) (j : Fin m) :
    (runBlock t m (some j)).card=bins t j.val := by simp [runBlock]

lemma runPalette_card (t m : ℕ) :
    Fintype.card (RunPalette t m)=(∑ j∈range m,bins t j)+16*t := by
  simp only [RunPalette,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range]

omit [Fintype V] [DecidableEq V] in
lemma stable_extend {A B : Type} [DecidableEq B] (G : SimpleGraph V)
    (e : A → B) (he : Function.Injective e) (S : A → Finset V)
    (hs : ∀ a, Stable G (S a)) (b : B) :
    Stable G (Function.extend e S (fun _ => ∅) b) := by
  by_cases hb : ∃ a,e a=b
  · obtain ⟨a,rfl⟩ := hb
    rw [he.extend_apply]
    exact hs a
  · rw [Function.extend_apply' _ _ _ hb]
    intro v hv
    simp at hv

theorem stage_cover_or_obstruction :
    ∃ T : ℝ, ∀ (t m : ℕ), T ≤ (t:ℝ) →
      (∀ j < m, (t:ℝ)/Real.log t ≤ rate t j ∧ rate t j ≤ 4*t) →
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → hadwigerNumber G < t →
      ∀ E : RunPalette t m → Finset V,
      (∀ (j : Fin m) (v : V), (bins t j.val:ℝ)/2 ≤
        (univ.filter (fun b => v ∈ E (stageBin t m j b))).card) →
      FractionalObstruction G ∨ ∀ k ≤ m, ∃ (R : Finset V) (S : RunPalette t m → Finset V),
        number (G.induce (↑R:Set V)) ≤ rate t k ∧
        (∀ b, Stable G (S b)) ∧
        (∀ b v, v∈S b → binIndex b < k) ∧
        (∀ v, v∉R → ∃ b, v∈S b ∧ v∈E b) := by
  classical
  obtain ⟨T,hT⟩ := Sampling.eligible_thinning_or_fractional_counterexample
  refine ⟨max T 2,?_⟩
  intro t m ht hvalid V _ _ G hord hminor E hE
  by_cases hob : FractionalObstruction G
  · exact Or.inl hob
  right
  have htT : T ≤ (t:ℝ) := (le_max_left _ _).trans ht
  have ht2 : (2:ℝ) ≤ t := (le_max_right _ _).trans ht
  have hn : 1 ≤ (t:ℝ)^(11/10:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  intro k hk
  induction k with
  | zero =>
    refine ⟨univ,fun _ => ∅,?_,?_,?_,?_⟩
    · rw [rate_zero]
      have hh := number_le_four G hob
      have hm : (hadwigerNumber G:ℝ) ≤ t := by exact_mod_cast hminor.le
      have hb : number G ≤ 4*(t:ℝ) := by linarith only [hh,hm]
      exact (number_comap G (Subtype.val : (↑(univ:Finset V):Set V) → V)).trans hb
    · intro b v hv; simp at hv
    · intro b v hv; simp at hv
    · intro v hv; exact (hv (mem_univ v)).elim
  | succ k ih =>
    obtain ⟨R,S,hf,hS,hsupp,hcover⟩ := ih (by omega)
    let j : Fin m := ⟨k,by omega⟩
    let H := G.induce (↑R:Set V)
    let E' (b : Fin (bins t k)) : Finset (↑R:Set V) :=
      univ.filter (fun v => v.val ∈ E (stageBin t m j b))
    have hE' (v : (↑R:Set V)) : (bins t k:ℝ)/2 ≤
        (univ.filter (fun b => v∈E' b)).card := by
      simpa only [E',mem_filter,mem_univ,true_and] using hE j v.val
    have hhord : (Fintype.card (↑R:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
      have hc : Fintype.card (↑R:Set V) ≤ Fintype.card V := Fintype.card_subtype_le _
      have hc' : (Fintype.card (↑R:Set V):ℝ) ≤ Fintype.card V := by exact_mod_cast hc
      exact hc'.trans hord
    have hhminor : hadwigerNumber H < t := (Knitting.model_induce G R).hadwiger_le.trans_lt hminor
    have hh := hT t ((t:ℝ)^(11/10:ℝ)) (rate t k) htT hn le_rfl
      (hvalid k (by omega)).1 (hvalid k (by omega)).2
      (↑R:Set V) H hhord hhminor hf E' hE'
    rcases hh with ⟨A,hA,hrem⟩ | hbad
    · change Fin (bins t k) → Finset (↑R:Set V) at A
      let Q : Finset (↑R:Set V) := univ\univ.biUnion (fun b => A b∩E' b)
      let R' := Q.image Subtype.val
      let e := stageBin t m j
      have he : Function.Injective e := stageBin_injective t m j
      let A' (b : Fin (bins t k)) : Finset V := (A b).image Subtype.val
      let D := Function.extend e A' (fun _ => ∅)
      have hD : ∀ b, Stable G (D b) := stable_extend G e he A' (fun b => stable_image (hA b))
      have hs (b : RunPalette t m) (hb : binIndex b=k) : S b=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have := hsupp b v hv
        omega
      have hds (b : RunPalette t m) (v : V) (hv : v∈D b) : binIndex b=k := by
        by_cases hb : ∃ a,e a=b
        · obtain ⟨a,rfl⟩ := hb; rfl
        · have hd : D b=∅ := Function.extend_apply' _ _ _ hb
          rw [hd] at hv
          simp at hv
      refine ⟨R',fun b => S b∪D b,?_,?_,?_,?_⟩
      · rw [←number_iso (induceImageIso G R Q),rate_succ]
        exact hrem
      · intro b
        change Stable G (S b∪D b)
        by_cases hb : binIndex b=k
        · rw [hs b hb,empty_union]; exact hD b
        · have hd : D b=∅ := eq_empty_iff_forall_notMem.mpr (fun v hv => hb (hds b v hv))
          rw [hd,union_empty]; exact hS b
      · intro b v hv
        rcases mem_union.mp hv with hv | hv
        · exact (hsupp b v hv).trans (Nat.lt_succ_self _)
        · rw [hds b v hv]; omega
      · intro v hv
        by_cases hvr : v∈R
        · let v' : (↑R:Set V) := ⟨v,hvr⟩
          have hvq : v'∉Q := fun hh => hv (mem_image.mpr ⟨v',hh,rfl⟩)
          have hva : v'∈univ.biUnion (fun b => A b∩E' b) := by
            by_contra h
            exact hvq (mem_sdiff.mpr ⟨mem_univ _,h⟩)
          obtain ⟨a,_,ha⟩ := mem_biUnion.mp hva
          refine ⟨e a,mem_union_right _ ?_,(mem_filter.mp (mem_inter.mp ha).2).2⟩
          change v ∈ Function.extend e A' (fun _ => ∅) (e a)
          erw [he.extend_apply]
          exact mem_image.mpr ⟨v',(mem_inter.mp ha).1,rfl⟩
        · obtain ⟨b,hb,hbe⟩ := hcover v hvr
          exact ⟨b,mem_union_left _ hb,hbe⟩
    · exact (hob (obstruction_induce G R hbad)).elim

lemma occupied_image_card {A B Color : Type} [Fintype A] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (L : Finset Color) (f : Color → B) :
    (ColorBins.occupied L (univ.map e) f).card=
      (univ.filter (fun a => ∃ c∈L, f c=e a)).card := by
  classical
  have he : ColorBins.occupied L (univ.map e) f =
      (univ.filter (fun a => ∃ c∈L, f c=e a)).map e := by
    ext b
    simp only [ColorBins.occupied,mem_inter,mem_map,mem_univ,true_and,mem_image,mem_filter]
    constructor
    · rintro ⟨⟨a,rfl⟩,c,hc,he⟩
      exact ⟨a,⟨c,hc,he⟩,rfl⟩
    · rintro ⟨a,⟨c,hc,he⟩,rfl⟩
      exact ⟨⟨a,rfl⟩,c,hc,he⟩
  rw [he,card_map]

lemma finish_cover (t m : ℕ) (G : SimpleGraph V) (ht : 1 < (t:ℝ))
    (horder : (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ))
    (hterm : rate t m < (t:ℝ)/Real.log t) (E : RunPalette t m → Finset V)
    (hE : ∀ v, 8*(t:ℝ) ≤ (univ.filter (fun b : Fin (16*t) => v∈E (Sum.inr b))).card)
    (R : Finset V) (S : RunPalette t m → Finset V)
    (hf : number (G.induce (↑R:Set V)) ≤ rate t m)
    (hS : ∀ b, Stable G (S b))
    (hsupp : ∀ b v, v∈S b → binIndex b < m)
    (hcover : ∀ v, v∉R → ∃ b, v∈S b ∧ v∈E b) :
    ∃ S' : RunPalette t m → Finset V, (∀ b, Stable G (S' b)) ∧
      ∀ v, ∃ b, v∈S' b ∧ v∈E b := by
  classical
  let E' (b : Fin (16*t)) : Finset (↑R:Set V) :=
    univ.filter (fun v => v.val ∈ E (Sum.inr b))
  have hord : (Fintype.card (↑R:Set V):ℝ) ≤ (t:ℝ)^(11/10:ℝ) := by
    have hc : (Fintype.card (↑R:Set V):ℝ) ≤ Fintype.card V := by
      exact_mod_cast Fintype.card_subtype_le (·∈(↑R:Set V))
    exact hc.trans horder
  obtain ⟨A,hA,hcov⟩ := Cleanup.cleanup_source (G.induce (↑R:Set V)) ht hord
    (hf.trans hterm.le) E' (fun v => by
      simpa only [E',mem_filter,mem_univ,true_and] using hE v.val)
  refine ⟨Sum.elim (fun b => S (Sum.inl b)) (fun b => (A b).image Subtype.val),?_,?_⟩
  · intro b
    rcases b with b | b
    · exact hS (Sum.inl b)
    · exact stable_image (hA b)
  · intro v
    by_cases hv : v∈R
    · obtain ⟨b,hbe,hba⟩ := hcov ⟨v,hv⟩
      exact ⟨Sum.inr b,mem_image.mpr ⟨⟨v,hv⟩,hba,rfl⟩,(mem_filter.mp hbe).2⟩
    · obtain ⟨b,hb,he⟩ := hcover v hv
      rcases b with b | b
      · exact ⟨Sum.inl b,hb,he⟩
      · have hh := hsupp (Sum.inr b) v hb
        simp only [binIndex,Sum.elim_inr] at hh
        omega

theorem choosable_or_fractional_obstruction :
    ∃ T : ℝ, ∀ (t : ℕ), T ≤ (t:ℝ) →
      ∀ (V : Type) [Fintype V] [DecidableEq V], ∀ G : SimpleGraph V,
      (Fintype.card V:ℝ) ≤ (t:ℝ)^(11/10:ℝ) → hadwigerNumber G < t →
      Choosable G (32768*t) ∨ FractionalObstruction G := by
  classical
  obtain ⟨T₀,hT₀⟩ := stage_cover_or_obstruction
  obtain ⟨T₁,hT₁⟩ := Filter.eventually_atTop.mp schedule_cutoff
  obtain ⟨T₂,hT₂⟩ := Filter.eventually_atTop.mp palette_tail_cutoff
  refine ⟨max T₀ (max T₁ T₂),?_⟩
  intro t ht V _ _ G hord hminor
  by_cases hob : FractionalObstruction G
  · exact Or.inr hob
  left
  have ht₀ := (le_max_left T₀ _).trans ht
  have ht₁ := ((le_max_left T₁ T₂).trans (le_max_right T₀ _)).trans ht
  have ht₂ := ((le_max_right T₁ T₂).trans (le_max_right T₀ _)).trans ht
  obtain ⟨ht1,hl,hlog,hp⟩ := hT₁ (t:ℝ) ht₁
  obtain ⟨m,hm,hterm,hvalid,hbudget,hblocks,hcleanup⟩ := schedule_exists t ht1 hl hlog hp
  have htN : 1 ≤ t := by exact_mod_cast (show (1:ℝ) ≤ t by linarith)
  have hb : 1 ≤ Fintype.card (RunPalette t m) := by rw [runPalette_card]; omega
  have hb' : (Fintype.card (RunPalette t m):ℝ) ≤ 4096*t := by
    rw [runPalette_card]
    exact_mod_cast hbudget
  intro Color L hL
  let u (j : Option (Fin m)) := (runBlock t m j).card
  let e : Option (Fin m) ≃ Fin (Fintype.card (Option (Fin m))) := Fintype.equivFin _
  have hj : (Fintype.card (Option (Fin m)):ℝ) ≤ (t:ℝ)+1 := by
    simp only [Fintype.card_option,Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    exact_mod_cast Nat.add_le_add_right hm 1
  have hu (j : Option (Fin m)) : (t:ℝ)^(7/10:ℝ) ≤ (u j:ℝ) := by
    cases j with
    | none => simpa only [u,runBlock_none,Nat.cast_mul,Nat.cast_ofNat] using hcleanup
    | some j => simpa only [u,runBlock_some] using hblocks j.val j.isLt
  have htail₀ := hT₂ (t:ℝ) ht₂ (Fintype.card V) (Fintype.card (RunPalette t m))
    (Fintype.card (Option (Fin m))) (fun i => u (e.symm i)) hord hb hb' hj (fun i => hu (e.symm i))
  have hsum : (∑ i : Fin (Fintype.card (Option (Fin m))),
      (2:ℝ)^(u (e.symm i))*Real.exp (-(32768*(t:ℝ))*(u (e.symm i))/(2*Fintype.card (RunPalette t m)))) =
      ∑ j : Option (Fin m), (2:ℝ)^(u j)*Real.exp (-(32768*(t:ℝ))*(u j)/(2*Fintype.card (RunPalette t m))) := by
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  rw [hsum] at htail₀
  have htail : (Fintype.card V:ℝ)*(∑ j, (2:ℝ)^(runBlock t m j).card*
      Real.exp (-(32768*t:ℕ)*(runBlock t m j).card/(2*Fintype.card (RunPalette t m)))) < 1 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,u] using htail₀
  obtain ⟨f,hf⟩ := ColorBins.exists_bins hb L (runBlock t m) hL htail
  let E (b : RunPalette t m) : Finset V := univ.filter (fun v => ∃ c∈L v, f c=b)
  have hEstage (j : Fin m) (v : V) : (bins t j.val:ℝ)/2 ≤
      (univ.filter (fun b => v∈E (stageBin t m j b))).card := by
    have hh := hf v (some j)
    rw [runBlock_some] at hh
    have he := occupied_image_card
      (⟨stageBin t m j,stageBin_injective t m j⟩ : Fin (bins t j.val) ↪ RunPalette t m) (L v) f
    change (ColorBins.occupied (L v) (runBlock t m (some j)) f).card=_ at he
    rw [he] at hh
    have hh' : (bins t j.val:ℝ) ≤ 2*(univ.filter (fun b => ∃ c∈L v, f c=stageBin t m j b)).card := by
      exact_mod_cast hh
    simpa only [E,mem_filter,mem_univ,true_and] using (show (bins t j.val:ℝ)/2 ≤
      (univ.filter (fun b => ∃ c∈L v, f c=stageBin t m j b)).card by linarith)
  have hEcleanup (v : V) : 8*(t:ℝ) ≤ (univ.filter (fun b : Fin (16*t) => v∈E (Sum.inr b))).card := by
    have hh := hf v none
    rw [runBlock_none] at hh
    have he := occupied_image_card (Function.Embedding.inr : Fin (16*t) ↪ RunPalette t m) (L v) f
    change (ColorBins.occupied (L v) (runBlock t m none) f).card=_ at he
    rw [he] at hh
    have hh' : 16*(t:ℝ) ≤ 2*(univ.filter (fun b : Fin (16*t) => ∃ c∈L v, f c=Sum.inr b)).card := by
      exact_mod_cast hh
    simpa only [E,mem_filter,mem_univ,true_and] using (show 8*(t:ℝ) ≤
      (univ.filter (fun b : Fin (16*t) => ∃ c∈L v, f c=Sum.inr b)).card by linarith)
  rcases hT₀ t m ht₀ hvalid V G hord hminor E hEstage with hbad | hstates
  · exact (hob hbad).elim
  obtain ⟨R,S,hrem,hS,hsupp,hcover⟩ := hstates m le_rfl
  obtain ⟨S',hS',hcover'⟩ := finish_cover t m G ht1 hord hterm E hEcleanup R S hrem hS hsupp hcover
  apply ColorBins.listColorable_of_bin_cover G L f S' hS'
  intro v
  obtain ⟨b,hb,he⟩ := hcover' v
  exact ⟨b,hb,(mem_filter.mp he).2⟩

end LinearListHadwiger.SmallList

end OAI
