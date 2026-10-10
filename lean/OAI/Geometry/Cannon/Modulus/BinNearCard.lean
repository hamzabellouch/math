import Mathlib
import OAI.Geometry.Cannon.Modulus.PathCellIndices

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
section
open Set Metric Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

lemma bin_near_card (n : ℕ) (offset s d : ℝ) (hs : 0 < s) :
    (univ.filter (fun i : Fin n => |d-(offset+(i:ℝ)*s)| ≤ 5*s)).card ≤ 11 := by
  classical
  let S := univ.filter (fun i : Fin n => |d-(offset+(i:ℝ)*s)| ≤ 5*s)
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,hmin⟩ := S.exists_min_image (fun i => i.val) hS
    have hsub : S.image (fun i => i.val) ⊆ Finset.Icc i.val (i.val+10) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
      refine Finset.mem_Icc.mpr ⟨hmin j hj,?_⟩
      have hi' := abs_le.mp (mem_filter.mp hi).2
      have hj' := abs_le.mp (mem_filter.mp hj).2
      have hr : (j.val:ℝ) ≤ (i.val:ℝ)+10 := by
        change -(5*s) ≤ d-(offset+(i.val:ℝ)*s) ∧ _ at hi'
        change -(5*s) ≤ d-(offset+(j.val:ℝ)*s) ∧ _ at hj'
        nlinarith
      exact_mod_cast hr
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
    exact hc.trans (by simp; omega)
  · change S.card ≤ 11
    rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    norm_num

theorem exists_radial_bins (A R s : ℝ) (hs : 0 < s) (hscale : 2*s ≤ R) :
    ∃ n : ℕ, ∃ bin : Fin n → ℝ,
      R/(2*s) ≤ (n:ℝ) ∧
      (∀ i, (A+1)*R ≤ bin i ∧ bin i ≤ (A+2)*R) ∧
      (∀ i j, i ≠ j → s ≤ |bin i-bin j|) ∧
      (∀ d, (univ.filter (fun i => |d-bin i| ≤ 5*s)).card ≤ 11) := by
  let n := ⌊R/s⌋₊
  let bin : Fin n → ℝ := fun i => (A+1)*R+(i:ℝ)*s
  have hR : 0 < R := by linarith
  have hrs : 0 ≤ R/s := div_nonneg hR.le hs.le
  have hfloor : (n:ℝ) ≤ R/s := Nat.floor_le hrs
  have hfloor' : R/s < (n:ℝ)+1 := Nat.lt_floor_add_one _
  refine ⟨n,bin,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2*s)).mpr
    have hf := (div_lt_iff₀ hs).mp hfloor'
    nlinarith
  · intro i
    have hi : (i:ℝ) < (n:ℝ) := by exact_mod_cast i.isLt
    have hni : (0:ℝ) ≤ (i:ℝ) := by positivity
    dsimp [bin]
    constructor
    · nlinarith
    · have hns := (le_div_iff₀ hs).mp hfloor
      nlinarith
  · intro i j hij
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hd : 1 ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
      rcases lt_or_gt_of_ne hv with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt h)))]
        have : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt h)))]
        have : (j.val:ℝ)+1 ≤ (i.val:ℝ) := by exact_mod_cast h
        linarith
    dsimp only [bin]
    rw [show (A+1)*R+(i:ℝ)*s-((A+1)*R+(j:ℝ)*s) = ((i:ℝ)-(j:ℝ))*s by ring,
      abs_mul,abs_of_pos hs]
    nlinarith
  · intro d
    exact bin_near_card n ((A+1)*R) s d hs

end CannonCapacity

end

section

open Filter Topology

namespace CannonCapacity

lemma subexponential_stretch (M : ℕ → ℝ)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j)
    (m : ℕ) (hm : 0 < m) (ell : ℝ) (hell : 0 < ell) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, M (m*n) ≤ C*Real.exp (ell*n) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨C,hC,hbound⟩ := hM (Real.exp (ell/m))
    (Real.one_lt_exp_iff.mpr (div_pos hell hm'))
  refine ⟨C,hC,fun n => ?_⟩
  have hh := hbound (m*n)
  rw [← Real.exp_nat_mul] at hh
  convert hh using 1
  congr 2
  push_cast
  field_simp

lemma eventually_exp_domination (a b C : ℝ) (hab : a < b) :
    ∀ᶠ n : ℕ in atTop, C*Real.exp (a*n) < Real.exp (b*n) := by
  have ht : Tendsto (fun n : ℕ => (b-a)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hab)
  have hh := (Real.tendsto_exp_atTop.comp ht).eventually (eventually_gt_atTop C)
  filter_upwards [hh] with n hn
  have hm := mul_lt_mul_of_pos_right hn (Real.exp_pos (a*n))
  dsimp only [Function.comp_apply] at hm
  rw [← Real.exp_add] at hm
  convert hm using 1; congr 1; ring

theorem eventually_capacity_thresholds (qdim : ℕ) (ell C N : ℝ)
    (hell : 0 < ell) (hC : 0 ≤ C) (hN : 0 < N) (M : ℕ → ℝ)
    (_hMnon : ∀ n, 0 ≤ M n)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ bins E : ℝ,
      Real.exp (2*ell*n)/2 ≤ bins →
      0 ≤ E → E ≤ C*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) →
      22*N ≤ Real.exp (-ell*n)*bins ∧
      484*E*N < Real.exp (8*(qdim+1)*ell*n)*bins^2 := by
  have hqdim : (0:ℝ) ≤ qdim := Nat.cast_nonneg _
  obtain ⟨C₁,hC₁,hstretch⟩ := subexponential_stretch M hM (160*(qdim+1)-2) (by omega) ell hell
  have hlarge := eventually_exp_domination 0 ell (44*N) hell
  have hsmall := eventually_exp_domination ((2*qdim+1)*ell) ((8*(qdim+1)+4)*ell)
    (1936*C*C₁*N) (by nlinarith only [hell,hqdim])
  filter_upwards [hlarge,hsmall] with n hn hn'
  simp only [zero_mul,Real.exp_zero,mul_one] at hn
  intro bins E hbins hE hEb
  have hx : 0 < Real.exp (ell*n) := Real.exp_pos _
  have hxn : 0 < Real.exp (-ell*n) := Real.exp_pos _
  have hx2 : 0 < Real.exp (2*ell*n) := Real.exp_pos _
  have hqq : 0 < Real.exp (8*(qdim+1)*ell*n) := Real.exp_pos _
  have hEbound : E ≤ C*C₁*Real.exp ((2*qdim+1)*ell*n) := by
    calc
      E ≤ C*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) := hEb
      _ ≤ C*Real.exp (2*qdim*ell*n)*(C₁*Real.exp (ell*n)) :=
        mul_le_mul_of_nonneg_left (hstretch n) (mul_nonneg hC (Real.exp_pos _).le)
      _ = _ := by rw [show C*Real.exp (2*qdim*ell*n)*(C₁*Real.exp (ell*n)) =
          C*C₁*(Real.exp (2*qdim*ell*n)*Real.exp (ell*n)) by ring,← Real.exp_add]; congr 2; ring
  constructor
  · have hm := mul_le_mul_of_nonneg_left hbins hxn.le
    have hid : Real.exp (-ell*n)*(Real.exp (2*ell*n)/2) = Real.exp (ell*n)/2 := by
      rw [← mul_div_assoc,← Real.exp_add]
      congr 2
      ring
    rw [hid] at hm
    linarith only [hm,hn]
  · have he := mul_le_mul_of_nonneg_right hEbound (by positivity : 0 ≤ (484:ℝ)*N)
    have hbnon : 0 ≤ bins := (div_pos hx2 (by norm_num)).le.trans hbins
    have hsquare := mul_le_mul hbins hbins (by positivity) hbnon
    have htarget := mul_le_mul_of_nonneg_left hsquare hqq.le
    have hid : Real.exp (8*(qdim+1)*ell*n)*((Real.exp (2*ell*n)/2)*(Real.exp (2*ell*n)/2)) =
        Real.exp ((8*(qdim+1)+4)*ell*n)/4 := by
      rw [show (Real.exp (2*ell*n)/2)*(Real.exp (2*ell*n)/2) =
        (Real.exp (2*ell*n)*Real.exp (2*ell*n))/4 by ring, ← mul_div_assoc,
        ← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    rw [hid] at htarget
    nlinarith only [he,htarget,hn']

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset CannonPacking CannonAnnular Filter Topology

attribute [local instance] Classical.propDecidable

theorem uniform_separated_capacity {X : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] (qdim : ℕ) (CP A B₀ H C c d₀ ell : ℝ)
    (hpack : PolynomialPacking (X:=X) qdim CP) (hCP : 0 ≤ CP)
    (hA : 1 ≤ A) (hAB : A+3 ≤ B₀) (hH : 0 < H)
    (hC : 0 ≤ C) (hc : 0 < c) (hdc : d₀ ≤ c) (hell : 0 < ell)
    (M : ℕ → ℝ) (hMnon : ∀ j, 0 ≤ M j)
    (hM : ∀ lam : ℝ, 1 < lam → ∃ C : ℝ, 0 < C ∧ ∀ j, M j ≤ C*lam^j) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι ζ δ : Type*} [Fintype ι] [Fintype ζ] [Fintype δ]
      (q : ι → X) (aux : ζ → X) (ξ : δ → X) (h : ζ → X ≃ₜ X)
      (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X)
      (lo hi t : ι → ℝ) (a b R r s : ℝ),
      a < b → 0 < R → 0 < r → 0 < s → r ≤ s → s ≤ R/4 →
      (B₀+1)*R ≤ 1 → max H 1*r ≤ 1 → 3*s ≤ 1 →
      max (C+2) (max c 1)*(r/s) ≤ 1 →
      R/s = Real.exp (2*ell*n) →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ i j, i ≠ j → s ≤ dist (aux i) (aux j)) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ z, dist x (aux z) ≤ (B₀+1)*R) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ i, dist (q i) v ≤ r) →
      (∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B₀+1)*R → ∃ z, dist v (aux z) ≤ s) →
      (∀ v, dist v x ≤ (B₀+2)*R → v ∈ Ω) →
      (∀ v ∈ Ioo a b, IsPreconnected (K v)) →
      (∀ v ∈ Ioo a b, ∃ y ∈ K v, dist y x ≤ A*R) →
      (∀ v ∈ Ioo a b, 2*B₀*R < diam (K v)) →
      (∀ v ∈ Ioo a b, ∀ y ∈ K v, y ∈ Ω → f y=v) →
      (∀ i, lo i ≤ hi i) → (∀ i, 0 ≤ t i) →
      (∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i) →
      (∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (lo i) (hi i)) →
      (∀ z v v', dist v (aux z) ≤ 3*s → dist v' (aux z) ≤ 3*s →
        dist (h z v) (h z v') ≤ C/s*dist v v' ∧ c/s*dist v v' ≤ dist (h z v) (h z v')) →
      ∀ ω : δ → ℝ, MacroscopicAdmissible ξ (r/s) d₀ ω →
      (∑ i, (ω i)^2) ≤ M ((160*(qdim+1)-2)*n) →
      ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
        1 ≤ ∑ i ∈ S, min (Real.exp (-ell*n)*t i) (Real.exp (8*(qdim+1)*ell*n)*(t i)^2) := by
  classical
  obtain ⟨Nt,hNt,htransfer⟩ := exists_local_transfer_constant qdim CP (C+2) c
    hpack hCP (by linarith) hc
  obtain ⟨Naux,hauxcount⟩ := exists_overlap_bound qdim CP 3 1 hpack hCP (by norm_num) zero_lt_one
  obtain ⟨Ndeg,hdegcount⟩ := exists_overlap_bound qdim CP H 1 hpack hCP hH zero_lt_one
  let N := Ndeg+1
  have hN : 0 < N := by dsimp [N]; omega
  have hB : 0 ≤ B₀+1 := by linarith
  let Ctotal := (Naux:ℝ)*CP*(B₀+1)^qdim*Nt
  have hCt : 0 ≤ Ctotal := by dsimp [Ctotal]; positivity
  have hthresh := eventually_capacity_thresholds qdim ell Ctotal N hell hCt
    (by exact_mod_cast hN) M hMnon hM
  filter_upwards [hthresh] with n hn
  intro ι ζ δ _ _ _ q aux ξ h x Ω f K lo hi t a b R r s hab hR hr hs hrs hsR
    hrad hdegscale hauxscale htransscale hratio hq haux hξ hauxloc hnet hauxnet hΩ
    hK hinner hdiam hlevel hlohi ht hlen hrange hmap ω hω hωmass
  obtain ⟨nb,bin,hnb,hbin,_hbinsep,hbinmul⟩ := exists_radial_bins A R s hs (by linarith)
  have hdegree (i : ι) : (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N := by
    exact (hdegcount q univ (q i) r hr hdegscale (by intro i _ j _ hij; simpa only [one_mul] using hq i j hij)).trans (by dsimp [N]; omega)
  have hmultaux (i : ι) : (univ.filter (fun z => dist (q i) (aux z) ≤ 3*s)).card ≤ Naux := by
    exact hauxcount aux univ (q i) s hs (by simpa using hauxscale) (by intro i _ j _ hij; simpa only [one_mul] using haux i j hij)
  have hcardaux : (Fintype.card ζ:ℝ) ≤ CP*(B₀+1)^qdim*Real.exp (2*qdim*ell*n) := by
    have hh := indexed_packing qdim CP hpack aux univ x ((B₀+1)*R) s hs
      (by nlinarith only [hsR,hA,hAB,hR]) hrad (by simpa using hauxloc) (by simpa using haux)
    simp only [card_univ] at hh
    have hid : CP*((B₀+1)*R/s)^qdim = CP*(B₀+1)^qdim*Real.exp (2*qdim*ell*n) := by
      rw [mul_div_assoc,hratio,mul_pow,← Real.exp_nat_mul, ← mul_assoc]
      congr 2
      ring
    exact hh.trans_eq hid
  let Etot := (Naux:ℝ)*Fintype.card ζ*(Nt*M ((160*(qdim+1)-2)*n))
  have hEtot : 0 ≤ Etot := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg hNt (hMnon _))
  have hEtotbound : Etot ≤ Ctotal*Real.exp (2*qdim*ell*n)*M ((160*(qdim+1)-2)*n) := by
    have hh := mul_le_mul_of_nonneg_left hcardaux (by positivity : (0:ℝ) ≤ Naux)
    have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hNt (hMnon ((160*(qdim+1)-2)*n)))
    convert hh' using 1; (try dsimp [Etot,Ctotal]); first | rfl | ring
  have hbinlower : Real.exp (2*ell*n)/2 ≤ (Fintype.card (Fin nb):ℝ) := by
    rw [← hratio,Fintype.card_fin]
    convert hnb using 1; ring
  obtain ⟨hlarge,hsmall⟩ := hn (Fintype.card (Fin nb)) Etot hbinlower hEtot hEtotbound
  apply node_separated_capacity q bin aux ξ h x Ω f K lo hi t a b A B₀ R r s C c d₀ H
    (Real.exp (-ell*n)) (Real.exp (8*(qdim+1)*ell*n)) Nt (M ((160*(qdim+1)-2)*n)) 11 N Naux
    hab hA (by linarith) hR hr hs hrs hsR hC hc hdc ?_ hnet hauxnet hΩ hK hinner hdiam hlevel
    hlohi ht hlen hrange (fun z v v' hv hv' => (hmap z v v' hv hv').1)
    (fun z v v' hv hv' => (hmap z v v' hv hv').2) ω hω hωmass ?_ hmultaux
    (Real.exp_pos _) (Real.exp_pos _) hNt (hMnon _) (by norm_num)
    (mul_nonneg hH.le hr.le) hN hdegree ?_ ?_ ?_
  · intro j
    obtain ⟨hl,hu⟩ := hbin j
    exact ⟨hl,hu.trans (by nlinarith only [hAB,hR])⟩
  · intro z
    exact htransfer q ξ (h z) (aux z) r s hr hs htransscale hq hξ
      (fun v v' hv hv' => (hmap z v v' hv hv').2) ω
  · intro i
    exact_mod_cast hbinmul (dist (q i) x)
  · linarith only [hlarge]
  · dsimp only [Etot] at hsmall
    nlinarith only [hsmall]

end CannonCapacity

end

namespace CannonCapacity

open Set Finset

attribute [local instance] Classical.propDecidable

lemma clip_mem {a b x : ℝ} (hab : a ≤ b) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma positive_clip_endpoints {a b l u : ℝ} (hab : a < b)
    (hlen : 0 < clip a b u-clip a b l) : l < b ∧ a < u := by
  constructor
  · by_contra hh
    have hbl : b ≤ l := le_of_not_gt hh
    have hclip : clip a b l = b := by simp only [clip,min_eq_left hbl,max_eq_right hab.le]
    rw [hclip] at hlen
    linarith only [hlen,(clip_mem (x := u) hab.le).2]
  · by_contra hh
    have hua : u ≤ a := le_of_not_gt hh
    have hclip : clip a b u = a := by
      simp only [clip,min_eq_right (hua.trans hab.le),max_eq_left hua]
    rw [hclip] at hlen
    linarith only [hlen,(clip_mem (x := l) hab.le).1]

lemma exists_wide_active_range {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (active : ι → Prop) (a b w : ℝ) (hab : a < b)
    (hlohi : ∀ i, lo i ≤ hi i) (hw : 0 ≤ w)
    (hcard : (Fintype.card ι : ℝ)*w < b-a)
    (hcover : ∀ s ∈ Ioo a b, ∃ i, active i ∧ s ∈ Icc (lo i) (hi i)) :
    ∃ i, active i ∧ w ≤ clip a b (hi i)-clip a b (lo i) := by
  classical
  have hh := CannonAnnular.weighted_open_interval_cover
    (fun i => clip a b (lo i)) (fun i => clip a b (hi i))
    (fun i => if active i then (1:ℝ) else 0) a b 1 hab.le
    (fun i => clip_mono a b (hlohi i)) (fun i => by split_ifs <;> norm_num) (by
      intro s hs
      obtain ⟨i,hai,his⟩ := hcover s hs
      calc
        1 = (Icc (clip a b (lo i)) (clip a b (hi i))).indicator
            (fun _ : ℝ => if active i then (1:ℝ) else 0) s := by
          rw [indicator_of_mem ((mem_clipped_iff hs).mpr his),ite_eq_left hai]
        _ ≤ ∑ j, (Icc (clip a b (lo j)) (clip a b (hi j))).indicator
            (fun _ : ℝ => if active j then (1:ℝ) else 0) s := by
          apply single_le_sum _ (mem_univ i)
          intro j _
          apply Set.indicator_nonneg
          intro _ _
          split_ifs <;> norm_num)
  simp only [one_mul] at hh
  by_contra hn
  have hbound : (∑ i, (if active i then (1:ℝ) else 0)*
      (clip a b (hi i)-clip a b (lo i))) ≤ (Fintype.card ι : ℝ)*w := by
    calc
      _ ≤ ∑ _i : ι, w := by
        apply sum_le_sum
        intro i _
        by_cases ha : active i
        · rw [ite_eq_left ha,one_mul]
          exact le_of_lt (lt_of_not_ge (fun hh => hn ⟨i,ha,hh⟩))
        · simp only [ite_eq_right ha,zero_mul]
          exact hw
      _ = _ := by simp
  linarith only [hh,hbound,hcard]

lemma small_outer_lower_end {a b l u : ℝ} (hab : a < b)
    (hl : l ≤ a+(b-a)/4)
    (hsmall : clip a b u-clip a b l < (b-a)/8) : u < a+3*(b-a)/8 := by
  by_contra hu
  have htarget : a+3*(b-a)/8 ≤ u := le_of_not_gt hu
  have hcL : clip a b l ≤ a+(b-a)/4 :=
    max_le (by linarith only [hab]) ((min_le_right _ _).trans hl)
  have hcU : a+3*(b-a)/8 ≤ clip a b u :=
    (le_min (by linarith only [hab]) htarget).trans (le_max_right _ _)
  linarith only [hsmall,hcL,hcU]

lemma small_outer_upper_start {a b l u : ℝ} (hab : a < b)
    (hu : a+3*(b-a)/4 ≤ u)
    (hsmall : clip a b u-clip a b l < (b-a)/8) : a+5*(b-a)/8 < l := by
  by_contra hl
  have htarget : l ≤ a+5*(b-a)/8 := le_of_not_gt hl
  have hcL : clip a b l ≤ a+5*(b-a)/8 :=
    max_le (by linarith only [hab]) ((min_le_right _ _).trans htarget)
  have hcU : a+3*(b-a)/4 ≤ clip a b u :=
    (le_min (by linarith only [hab]) hu).trans (le_max_right _ _)
  linarith only [hsmall,hcL,hcU]

theorem bad_node_large_range {ι : Type*} [Fintype ι]
    (li ui lo uo : ι → ℝ) (near : ι → Prop) (a b κ : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι : ℝ)*κ ≤ 1/8)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hcover : ∀ s ∈ Ioo a b, ∃ i, near i ∧ s ∈ Icc (li i) (ui i))
    (hbad : ¬ ∃ i j,
      κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
      κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
      uo i+(b-a)/4 ≤ lo j) :
    ∃ i, near i ∧ (b-a)/8 ≤ clip a b (uo i)-clip a b (lo i) := by
  have hΔ : 0 < b-a := sub_pos.mpr hab
  have hw : 0 < κ*(b-a) := mul_pos hκ hΔ
  have hcount' : (Fintype.card ι : ℝ)*(κ*(b-a)) ≤ (b-a)/8 := by nlinarith only [hcount,hΔ]
  obtain ⟨i,hni,hwi⟩ := exists_wide_active_range li ui near a (a+(b-a)/4) (κ*(b-a))
    (by linarith only [hab]) hinner hw.le (by linarith only [hcount',hΔ]) (by
      intro s hs
      apply hcover s
      exact ⟨hs.1,by linarith only [hs.2,hab]⟩)
  obtain ⟨j,hnj,hwj⟩ := exists_wide_active_range li ui near (a+3*(b-a)/4) b (κ*(b-a))
    (by linarith only [hab]) hinner hw.le (by linarith only [hcount',hΔ]) (by
      intro s hs
      apply hcover s
      exact ⟨by linarith only [hs.1,hab],hs.2⟩)
  by_contra hn
  have hsi : clip a b (uo i)-clip a b (lo i) < (b-a)/8 :=
    lt_of_not_ge (fun h => hn ⟨i,hni,h⟩)
  have hsj : clip a b (uo j)-clip a b (lo j) < (b-a)/8 :=
    lt_of_not_ge (fun h => hn ⟨j,hnj,h⟩)
  have hiend := (positive_clip_endpoints (by linarith only [hab]) (hw.trans_le hwi)).1
  have hjstart := (positive_clip_endpoints (by linarith only [hab]) (hw.trans_le hwj)).2
  have he := small_outer_lower_end hab ((hlo i).trans hiend.le) hsi
  have hs := small_outer_upper_start hab (hjstart.le.trans (huo j)) hsj
  exact hbad ⟨i,j,hwi,hwj,by linarith only [he,hs]⟩

end CannonCapacity

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

theorem node_radial_cover {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (Ω : Set X) (f : X → ℝ) (K : ℝ → Set X)
    (li ui : ι → ℝ) (a b A B R r rad : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hA : 0 ≤ A) (hrad : A*R ≤ rad ∧ rad ≤ B*R)
    (hnet : ∀ v, (A-1)*R ≤ dist v x → dist v x ≤ (B+1)*R → ∃ i, dist (q i) v ≤ r)
    (hΩ : ∀ v, dist v x ≤ (B+1)*R → v ∈ Ω)
    (hK : ∀ t ∈ Ioo a b, IsPreconnected (K t))
    (hinner : ∀ t ∈ Ioo a b, ∃ y ∈ K t, dist y x ≤ A*R)
    (hdiam : ∀ t ∈ Ioo a b, 2*B*R < diam (K t))
    (hlevel : ∀ t ∈ Ioo a b, ∀ v ∈ K t, v ∈ Ω → f v=t)
    (hrange : ∀ i v, v ∈ Ω → dist v (q i) ≤ 2*r → f v ∈ Icc (li i) (ui i)) :
    ∀ t ∈ Ioo a b, ∃ i, |dist (q i) x-rad| ≤ r ∧ t ∈ Icc (li i) (ui i) := by
  intro t ht
  obtain ⟨w,hw,hwr⟩ := level_radial_hit x (K t) (hK t ht)
    ((mul_nonneg hA hR.le).trans hrad.1)
    (by obtain ⟨y,hy,hyD⟩ := hinner t ht; exact ⟨y,hy,hyD.trans hrad.1⟩)
    (by nlinarith only [hdiam t ht,hrad.2])
  obtain ⟨i,hi⟩ := hnet w (by rw [hwr]; nlinarith only [hrad.1,hR])
    (by rw [hwr]; nlinarith only [hrad.2,hR])
  have hwΩ := hΩ w (by rw [hwr]; nlinarith only [hrad.2,hR])
  refine ⟨i,?_,?_⟩
  · rw [← hwr]
    exact (abs_dist_sub_le (q i) w x).trans hi
  · rw [← hlevel t ht w hw hwΩ]
    apply hrange i w hwΩ
    rw [dist_comm]
    linarith only [hi,hr]

theorem bad_node_many_children {X : Type*} [MetricSpace X] {ι : Type*} [Fintype ι]
    (q : ι → X) (x : X) (li ui lo uo t : ι → ℝ) (a b κ A B R r H : ℝ)
    (hab : a < b) (hκ : 0 < κ) (hcount : (Fintype.card ι:ℝ)*κ ≤ 1/8)
    (hR : 0 < R) (hr : 0 < r) (hH : 0 < H) (hAB : A+2 ≤ B)
    (hscale : 2*((H+3)*r) ≤ R)
    (hinner : ∀ i, li i ≤ ui i) (hlo : ∀ i, lo i ≤ li i) (huo : ∀ i, ui i ≤ uo i)
    (hlen : ∀ i, clip a b (uo i)-clip a b (lo i) = (b-a)*t i)
    (hcover : ∀ rad, A*R ≤ rad → rad ≤ B*R → ∀ s ∈ Ioo a b,
      ∃ i, |dist (q i) x-rad| ≤ r ∧ s ∈ Icc (li i) (ui i))
    (hbad : ¬ ∃ i j,
      κ*(b-a) ≤ clip a (a+(b-a)/4) (ui i)-clip a (a+(b-a)/4) (li i) ∧
      κ*(b-a) ≤ clip (a+3*(b-a)/4) b (ui j)-clip (a+3*(b-a)/4) b (li j) ∧
      uo i+(b-a)/4 ≤ lo j) :
    ∃ S : Finset ι, R/(2*(H+3)*r) ≤ (S.card:ℝ) ∧
      (∀ i ∈ S, 1/8 ≤ t i) ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j) := by
  classical
  obtain ⟨n,bin,hnb,hbin,hsep,_⟩ := exists_radial_bins A R ((H+3)*r)
    (mul_pos (by linarith) hr) hscale
  have hchoose (z : Fin n) : ∃ i, |dist (q i) x-bin z| ≤ r ∧ 1/8 ≤ t i := by
    obtain ⟨i,hi,ht⟩ := bad_node_large_range li ui lo uo
      (fun i => |dist (q i) x-bin z| ≤ r) a b κ hab hκ hcount hinner hlo huo
      (hcover (bin z) (by nlinarith only [(hbin z).1,hR])
        (by nlinarith only [(hbin z).2,hAB,hR])) hbad
    refine ⟨i,hi,?_⟩
    rw [hlen] at ht
    nlinarith only [ht,hab]
  choose choose hnear ht using hchoose
  have hdist {z w : Fin n} (hzw : z ≠ w) : H*r < dist (q (choose z)) (q (choose w)) := by
    have hz := hnear z
    have hw := hnear w
    have hm := hsep z w hzw
    have hd := abs_dist_sub_le (q (choose z)) (q (choose w)) x
    have htri : |bin z-bin w| ≤ |bin z-dist (q (choose z)) x| +
        |dist (q (choose z)) x-dist (q (choose w)) x| +
        |dist (q (choose w)) x-bin w| := by
      simpa only [Real.dist_eq] using dist_triangle4 (bin z)
        (dist (q (choose z)) x) (dist (q (choose w)) x) (bin w)
    rw [abs_sub_comm (bin z) (dist (q (choose z)) x)] at htri
    nlinarith only [hz,hw,hm,hd,htri,hr]
  have hinj : Function.Injective choose := by
    intro z w hzw
    by_contra hn
    have hd := hdist hn
    rw [hzw,dist_self] at hd
    have hh := mul_pos hH hr
    linarith only [hd,hh]
  refine ⟨univ.image choose,?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ hinj,card_univ,Fintype.card_fin]
    convert hnb using 1; ring
  · intro i hi
    obtain ⟨z,_,rfl⟩ := mem_image.mp hi
    exact ht z
  · intro i hi j hj hij
    obtain ⟨z,_,rfl⟩ := mem_image.mp hi
    obtain ⟨w,_,rfl⟩ := mem_image.mp hj
    exact hdist (fun hz => hij (congrArg choose hz))

end CannonCapacity

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
