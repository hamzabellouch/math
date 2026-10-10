import OAI.NumberTheory.PrimeGaps.EulerFactors

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

noncomputable def fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) : Finset (Finset ι) := by
  classical
  exact R.biUnion fun r => nonemptySubsets (Finset.univ.filter fun i => b i=r)

theorem mem_fiberSubsetFamily {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (S : Finset ι) :
    S∈fiberSubsetFamily b R ↔ S.Nonempty ∧ ∃ r∈R, ∀ i∈S, b i=r := by
  classical
  simp only [fiberSubsetFamily, Finset.mem_biUnion, mem_nonemptySubsets]
  constructor
  · rintro ⟨r,hr,hS,hsub⟩
    exact ⟨hS,r,hr,fun i hi => (Finset.mem_filter.mp (hsub hi)).2⟩
  · rintro ⟨hS,r,hr,hsub⟩
    exact ⟨r,hr,hS,fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i hi⟩⟩

theorem disjoint_nonemptySubsets_fibers {ι α : Type*} [Fintype ι] (b : ι → α)
    {r s : α} (hrs : r≠s) :
    Disjoint (nonemptySubsets (Finset.univ.filter fun i => b i=r))
      (nonemptySubsets (Finset.univ.filter fun i => b i=s)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro S hSr hSs
  rcases mem_nonemptySubsets.mp hSr with ⟨hS,hR⟩
  have hT := (mem_nonemptySubsets.mp hSs).2
  rcases hS with ⟨i,hi⟩
  exact hrs ((Finset.mem_filter.mp (hR hi)).2.symm.trans (Finset.mem_filter.mp (hT hi)).2)

theorem fiberSubsetFamily_sign_sum {ι α : Type*} [Fintype ι] (b : ι → α)
    (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    (∑ S∈fiberSubsetFamily b R, (-1:ℤ)^S.card) = -(R.card:ℤ) := by
  classical
  rw [fiberSubsetFamily, Finset.sum_biUnion]
  · have hs (r : α) (hr : r∈R) : (Finset.univ.filter fun i => b i=r).Nonempty := by
      rcases hR r hr with ⟨i,hi⟩
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    calc
      _ = ∑ _r∈R, (-1:ℤ) := Finset.sum_congr rfl (fun r hr => sum_nonemptySubsets_sign (hs r hr))
      _ = _ := by simp
  · intro r _ s _ hrs
    exact disjoint_nonemptySubsets_fibers b hrs

theorem mem_fiberSubsetFamily_image {ι α : Type*} [Fintype ι] [DecidableEq α] (b : ι → α)
    (S : Finset ι) :
    S∈fiberSubsetFamily b (Finset.univ.image b) ↔
      S.Nonempty ∧ ∀ i∈S, ∀ j∈S, b i=b j := by
  classical
  rw [mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,_,hb⟩
    exact ⟨hS,fun i hi j hj => (hb i hi).trans (hb j hj).symm⟩
  · rintro ⟨hS,hb⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩,b i,Finset.mem_image_of_mem _ (Finset.mem_univ _),fun j hj => hb j hj i hi⟩

theorem eulerP_zero_fiber_family {ι α : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (hR : ∀ r∈R, ∃ i, b i=r) :
    eulerP p δ (fiberSubsetFamily b R) (fun _ => 0) =
      1-((p:ℂ)-δ)⁻¹*(R.card:ℂ) := by
  have hs : (∑ S∈fiberSubsetFamily b R, (-1:ℂ)^S.card) = -(R.card:ℂ) := by
    exact_mod_cast fiberSubsetFamily_sign_sum b R hR
  simp only [eulerP, primeMonomial_zero, mul_one, hs]
  ring

theorem eulerH_zero_fiber_families {ι α β : Type*} [Fintype ι]
    (p δ : ℕ) (b : ι → α) (R : Finset α) (c : ι → β) (T : Finset β)
    (hR : ∀ r∈R, ∃ i, b i=r) (hT : ∀ t∈T, ∃ i, c i=t)
    (hp : 1-(p:ℂ)⁻¹≠0) :
    eulerH p δ (fiberSubsetFamily b R) (fiberSubsetFamily c T) (fun _ => 0) =
      (1-((p:ℂ)-δ)⁻¹*(R.card:ℂ))*(1-(p:ℂ)⁻¹)^(-(T.card:ℤ)) := by
  rw [eulerH, eulerP_zero_fiber_family p δ b R hR]
  simp only [primeMonomial_zero, mul_one]
  rw [prod_const_zpow _ _ hp, fiberSubsetFamily_sign_sum c T hT]

noncomputable def shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) : Finset (Finset ι) :=
  fiberSubsetFamily b (Finset.univ.image b)

noncomputable def residueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) : Finset (Finset ι) :=
  fiberSubsetFamily (fun i => b i%(p:ℤ)) (Finset.univ.image fun i => b i%(p:ℤ))

noncomputable def markedResidueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) : Finset (Finset ι) :=
  fiberSubsetFamily (fun i => b i%(p:ℤ)) ((Finset.univ.image fun i => b i%(p:ℤ)).erase (a%(p:ℤ)))

theorem mem_markedResidueFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ) (S : Finset ι) :
    S∈markedResidueFamily b p a ↔ S.Nonempty ∧
      (∀ i∈S, ∀ j∈S, b i%(p:ℤ)=b j%(p:ℤ)) ∧ ∀ i∈S, b i%(p:ℤ)≠a%(p:ℤ) := by
  rw [markedResidueFamily, mem_fiberSubsetFamily]
  constructor
  · rintro ⟨hS,r,hr,hb⟩
    exact ⟨hS,(fun i hi j hj => (hb i hi).trans (hb j hj).symm),fun i hi =>
      (hb i hi) ▸ (Finset.mem_erase.mp hr).1⟩
  · rintro ⟨hS,hb,ha⟩
    rcases hS with ⟨i,hi⟩
    exact ⟨⟨i,hi⟩, b i%(p:ℤ),Finset.mem_erase.mpr ⟨ha i hi,
      Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩,fun j hj => hb j hj i hi⟩

theorem residueFamily_eq_shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) : residueFamily b p=shiftFamily b := by
  apply Finset.ext
  intro S
  constructor
  · intro hs
    rcases (mem_fiberSubsetFamily_image (fun i => b i%(p:ℤ)) S).mp hs with ⟨hn,he⟩
    exact (mem_fiberSubsetFamily_image b S).mpr ⟨hn,fun i hi j hj => h i j (he i hi j hj)⟩
  · intro hs
    rcases (mem_fiberSubsetFamily_image b S).mp hs with ⟨hn,he⟩
    exact (mem_fiberSubsetFamily_image (fun i => b i%(p:ℤ)) S).mpr
      ⟨hn,fun i hi j hj => congrArg (fun a => a%(p:ℤ)) (he i hi j hj)⟩

theorem markedResidueFamily_eq_shiftFamily {ι : Type*} [Fintype ι] (b : ι → ℤ) (p : ℕ) (a : ℤ)
    (h : ∀ i j, b i%(p:ℤ)=b j%(p:ℤ) → b i=b j) (ha : ∀ i, b i%(p:ℤ)≠a%(p:ℤ)) :
    markedResidueFamily b p a=shiftFamily b := by
  rw [markedResidueFamily]
  have hn : a%(p:ℤ)∉(Finset.univ.image fun i => b i%(p:ℤ)) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨i,_,hi⟩
    exact ha i hi
  rw [Finset.erase_eq_of_notMem hn]
  exact residueFamily_eq_shiftFamily b p h

theorem one_sub_prime_inv_ne_zero {p : ℕ} (hp : 2≤p) : 1-(p:ℂ)⁻¹≠0 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hr : 1-(p:ℝ)⁻¹≠0 := by
    have := (inv_lt_one₀ (by linarith : 0<(p:ℝ))).mpr (by linarith : 1<(p:ℝ))
    linarith
  have hc : ((1-(p:ℝ)⁻¹:ℝ):ℂ)≠0 := by exact_mod_cast hr
  simpa using hc

theorem eulerH_unmarked_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) {p : ℕ} (hp : 2≤p) :
    eulerH p 0 (residueFamily b p) (shiftFamily b) (fun _ => 0) =
      (singularLocal (Finset.univ.image b) p : ℂ) := by
  rw [residueFamily, shiftFamily, eulerH_zero_fiber_families p 0 _ _ _ _
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (one_sub_prime_inv_ne_zero hp)]
  simp only [Nat.cast_zero, sub_zero, zpow_neg, zpow_natCast, singularLocal, residueCount,
    Finset.image_image, Function.comp_def]
  push_cast
  simp only [div_eq_mul_inv]
  ring

theorem residueCount_insert_eq (H : Finset ℤ) (p : ℕ) (a : ℤ) :
    residueCount (insert a H) p = ((H.image fun b => b%(p:ℤ)).erase (a%(p:ℤ))).card+1 := by
  unfold residueCount
  rw [Finset.image_insert]
  have h := Finset.card_erase_add_one (Finset.mem_insert_self (a%(p:ℤ))
    (H.image fun b => b%(p:ℤ)))
  simpa only [Finset.erase_insert_eq_erase] using h.symm

theorem eulerH_marked_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) {p : ℕ} (hp : 2≤p) :
    eulerH p 1 (markedResidueFamily b p a) (shiftFamily b) (fun _ => 0) =
      (singularLocal (insert a (Finset.univ.image b)) p : ℂ) := by
  have ha' : a∉Finset.univ.image b := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, not_exists] using ha
  rw [markedResidueFamily, shiftFamily, eulerH_zero_fiber_families p 1 _ _ _ _
    (fun r hr => by
      rcases Finset.mem_image.mp (Finset.mem_erase.mp hr).2 with ⟨i,_,hi⟩
      exact ⟨i,hi⟩)
    (fun r hr => by rcases Finset.mem_image.mp hr with ⟨i,_,hi⟩; exact ⟨i,hi⟩)
    (one_sub_prime_inv_ne_zero hp)]
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast (by omega : p≠0)
  have hp1 : (p:ℂ)-1≠0 := by
    intro he
    have hh : (p:ℂ)=1 := sub_eq_zero.mp he
    have : p=1 := by exact_mod_cast hh
    omega
  have hpinv := one_sub_prime_inv_ne_zero hp
  simp only [Nat.cast_one, zpow_neg, zpow_natCast, singularLocal,
    residueCount_insert_eq, Finset.card_insert_of_notMem ha', Finset.image_image, Function.comp_def]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem multipliable_of_summable_norm_sub_one {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) : Multipliable f := by
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hf

theorem norm_tprod_sub_one_le_exp {ι : Type*} {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-1‖≤Real.exp (∑' i, ‖f i-1‖)-1 := by
  have hm := multipliable_of_summable_norm_sub_one hf
  apply le_of_tendsto ((hm.hasProd.sub_const 1).norm)
  filter_upwards [] with S
  calc
    _ ≤ Real.exp (∑ i∈S, ‖f i-1‖)-1 := by
      simpa only [add_sub_cancel] using Finset.norm_prod_one_add_sub_one_le S (fun i => f i-1)
    _ ≤ _ := sub_le_sub_right (Real.exp_le_exp.mpr (hf.sum_le_tsum S (fun _ _ => norm_nonneg _))) 1

theorem tprod_eq_prod_mul_tail {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    (∏' i, f i) = (∏ i∈S, f i)*(∏' i : {i // i∉S}, f i) := by
  classical
  have hs := multipliable_of_summable_norm_sub_one (hf.subtype (fun i => i∈S))
  have ht := multipliable_of_summable_norm_sub_one (hf.subtype (fun i => i∉S))
  have hh := hs.tprod_mul_tprod_compl ht
  rw [Finset.tprod_subtype'] at hh
  exact hh.symm

theorem norm_tprod_sub_prod_le {ι : Type*} (S : Finset ι) {f : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) :
    ‖(∏' i, f i)-(∏ i∈S, f i)‖ ≤
      ‖∏ i∈S, f i‖*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1) := by
  rw [tprod_eq_prod_mul_tail S hf, ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_tprod_sub_one_le_exp (hf.subtype (fun i => i∉S))) (norm_nonneg _)

theorem norm_tprod_sub_tprod_le {ι : Type*} (S : Finset ι) {f g : ι → ℂ}
    (hf : Summable (fun i => ‖f i-1‖)) (hg : Summable (fun i => ‖g i-1‖))
    (B e : ι → ℝ) (hB : ∀ i∈S, 1≤B i)
    (hfn : ∀ i∈S, ‖f i‖≤B i) (hgn : ∀ i∈S, ‖g i‖≤B i)
    (he : ∀ i∈S, ‖f i-g i‖≤e i) :
    ‖(∏' i, f i)-(∏' i, g i)‖ ≤ (∏ i∈S, B i)*
      ((∑ i∈S, e i)+(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1)) := by
  have hpf : ‖∏ i∈S, f i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfn
  have hpg : ‖∏ i∈S, g i‖≤∏ i∈S, B i := by
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hgn
  have hdf := norm_tprod_sub_prod_le S hf
  have hdg := norm_tprod_sub_prod_le S hg
  have hp := norm_prod_sub_prod_le S f g B e hB hfn hgn he
  have hfp : 0≤Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have hgp : 0≤Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1 :=
    sub_nonneg.mpr (Real.one_le_exp (tsum_nonneg fun _ => norm_nonneg _))
  have htri := norm_sub_le_norm_sub_add_norm_sub (∏' i, f i) (∏ i∈S, f i) (∏' i, g i)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (∏ i∈S, f i) (∏ i∈S, g i) (∏' i, g i)
  rw [norm_sub_rev (∏ i∈S, g i)] at htri'
  calc
    _ ≤ ‖(∏' i, f i)-(∏ i∈S, f i)‖+‖(∏ i∈S, f i)-(∏ i∈S, g i)‖+
        ‖(∏' i, g i)-(∏ i∈S, g i)‖ := by linarith
    _ ≤ (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖f i-1‖)-1)+
        (∏ i∈S, B i)*(∑ i∈S, e i)+
        (∏ i∈S, B i)*(Real.exp (∑' i : {i // i∉S}, ‖g i-1‖)-1) := by
      exact add_le_add (add_le_add (hdf.trans (mul_le_mul_of_nonneg_right hpf hfp)) hp)
        (hdg.trans (mul_le_mul_of_nonneg_right hpg hgp))
    _ = _ := by ring

theorem sum_reciprocal_sq_injective_le {ι : Type*} (S : Finset ι) (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i∈S, y<n i) :
    (∑ i∈S, (1:ℝ)/(n i:ℝ)^2) ≤ 1/(y:ℝ) := by
  classical
  rw [← Finset.sum_image (f := fun k : ℕ => (1:ℝ)/(k:ℝ)^2) (fun _ _ _ _ h => hn h)]
  apply sum_reciprocal_sq_le hy
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨i,hi,rfl⟩
  exact hl i hi

theorem summable_tsum_le_of_reciprocal_sq {ι : Type*} (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i, y<n i)
    (f : ι → ℝ) {K : ℝ} (hK : 0≤K) (hf : ∀ i, 0≤f i)
    (hbound : ∀ i, f i≤K/(n i:ℝ)^2) :
    Summable f ∧ (∑' i, f i)≤K/(y:ℝ) := by
  have hh (S : Finset ι) : (∑ i∈S, f i)≤K/(y:ℝ) := by
    calc
      _ ≤ ∑ i∈S, K/(n i:ℝ)^2 := Finset.sum_le_sum fun i _ => hbound i
      _ = K*(∑ i∈S, (1:ℝ)/(n i:ℝ)^2) := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
      _ ≤ K*(1/(y:ℝ)) := mul_le_mul_of_nonneg_left
        (sum_reciprocal_sq_injective_le S n hn hy (fun i _ => hl i)) hK
      _ = _ := by ring
  exact ⟨summable_of_sum_le hf hh, Real.tsum_le_of_sum_le hf hh⟩

theorem norm_euler_tail_sub_one_le {ι : Type*} (n : ι → ℕ)
    (hn : Function.Injective n) {y : ℕ} (hy : 0<y) (hl : ∀ i, y<n i)
    (f : ι → ℂ) {K : ℝ} (hK : 0≤K)
    (hbound : ∀ i, ‖f i-1‖≤K/(n i:ℝ)^2) :
    Multipliable f ∧ ‖(∏' i, f i)-1‖≤Real.exp (K/(y:ℝ))-1 := by
  have hh := summable_tsum_le_of_reciprocal_sq n hn hy hl (fun i => ‖f i-1‖) hK
    (fun _ => norm_nonneg _) hbound
  exact ⟨multipliable_of_summable_norm_sub_one hh.1,
    (norm_tprod_sub_one_le_exp hh.1).trans (sub_le_sub_right (Real.exp_le_exp.mpr hh.2) 1)⟩

end LargePrimeGaps

end OAI
