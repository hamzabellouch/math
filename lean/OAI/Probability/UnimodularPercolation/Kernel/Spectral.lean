import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Sprinkling

namespace OAI

/-! Isoperimetric energy, symmetric walks and invariant operator traces. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section IsoperimetricEnergy
attribute [local instance] Classical.propDecidable

 
noncomputable def levelIndicator (a t : ℝ) : ℝ := if 0 ≤ t ∧ t < a then 1 else 0

theorem levelIndicator_eq (a : ℝ) :
    levelIndicator a = Set.indicator (Set.Ico 0 a) (fun _ => (1:ℝ)) := by
  funext t
  simp [levelIndicator, Set.indicator_apply, Set.mem_Ico]

theorem integrable_levelIndicator (a : ℝ) : Integrable (levelIndicator a) := by
  rw [levelIndicator_eq]
  exact (integrableOn_const (isCompact_Icc.measure_lt_top.ne) :
    IntegrableOn (fun _ : ℝ => (1:ℝ)) (Set.Icc 0 a)).mono_set
      Set.Ico_subset_Icc_self |>.integrable_indicator measurableSet_Ico

theorem integral_levelIndicator {a : ℝ} (ha : 0 ≤ a) :
    ∫ t, levelIndicator a t = a := by
  rw [levelIndicator_eq, integral_indicator measurableSet_Ico]
  simp [ha]

theorem abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (fun t => |levelIndicator a t - levelIndicator b t|) =
      Set.indicator (Set.Ico (min a b) (max a b)) (fun _ => (1:ℝ)) := by
  funext t
  rcases le_total a b with hab | hba
  · simp only [min_eq_left hab, max_eq_right hab, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases hta : t < a
      · have htb : t < b := hta.trans_le hab
        have hna : ¬a ≤ t := not_le.mpr hta
        simp [ht,hta,htb,hna]
      · by_cases htb : t < b <;> simp [ht,hta,htb,le_of_not_gt hta]
    · have hna : ¬a ≤ t := fun h => ht (ha.trans h)
      simp [ht,hna]
  · simp only [min_eq_right hba, max_eq_left hba, Set.indicator_apply, Set.mem_Ico,
      levelIndicator]
    by_cases ht : 0 ≤ t
    · by_cases htb : t < b
      · have hta : t < a := htb.trans_le hba
        have hnb : ¬b ≤ t := not_le.mpr htb
        simp [ht,hta,htb,hnb]
      · by_cases hta : t < a <;> simp [ht,hta,htb,le_of_not_gt htb]
    · have hnb : ¬b ≤ t := fun h => ht (hb.trans h)
      simp [ht,hnb]

theorem integrable_abs_sub_levelIndicator (a b : ℝ) :
    Integrable (fun t => |levelIndicator a t - levelIndicator b t|) :=
  ((integrable_levelIndicator a).sub (integrable_levelIndicator b)).abs

theorem integral_abs_sub_levelIndicator {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ t, |levelIndicator a t - levelIndicator b t| = |a-b| := by
  rw [abs_sub_levelIndicator ha hb, integral_indicator measurableSet_Ico]
  simp only [setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Ico_of_le min_le_max]
  exact (max_sub_min_eq_abs a b).trans (abs_sub_comm _ _)

 
theorem finite_coarea_lower_bound {α : Type*} (S : Finset α) (P : Finset (α × α))
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) (h : ℝ)
    (hcut : ∀ A : Finset α, A ⊆ S →
      h * A.card ≤ ∑ e ∈ P,
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)|) :
    h * ∑ x ∈ S, f x ≤ ∑ e ∈ P, |f e.1 - f e.2| := by
  let F : ℝ → ℝ := fun t => h * ∑ x ∈ S, levelIndicator (f x) t
  let J : ℝ → ℝ := fun t => ∑ e ∈ P,
    |levelIndicator (f e.1) t - levelIndicator (f e.2) t|
  have hF : Integrable F :=
    (integrable_finsetSum S (fun x _ => integrable_levelIndicator (f x))).const_mul h
  have hJ : Integrable J :=
    integrable_finsetSum P (fun e _ => integrable_abs_sub_levelIndicator _ _)
  have hle : ∀ t, F t ≤ J t := by
    intro t
    let A := S.filter (fun x => 0 ≤ t ∧ t < f x)
    have hi (x : α) : levelIndicator (f x) t = if x ∈ A then (1:ℝ) else 0 := by
      by_cases hx : x ∈ S
      · simp [A,levelIndicator,hx]
      · rw [hout x hx]
        have hz : ¬(0 ≤ t ∧ t < 0) := fun ht => (not_lt_of_ge ht.1) ht.2
        simp [A,levelIndicator,hx,hz]
    have hc : ∑ x ∈ S, levelIndicator (f x) t = (A.card : ℝ) := by
      simp [levelIndicator,A,Finset.sum_boole]
    dsimp [F,J]
    rw [hc]
    simpa only [hi] using hcut A (Finset.filter_subset _ _)
  have H := integral_mono hF hJ hle
  dsimp [F,J] at H
  rw [integral_const_mul, integral_finsetSum _
    (fun x _ => integrable_levelIndicator (f x)), integral_finsetSum _
    (fun e _ => integrable_abs_sub_levelIndicator _ _)] at H
  simpa only [integral_levelIndicator (hf _),
    integral_abs_sub_levelIndicator (hf _) (hf _)] using H

theorem hV_mul_card_le (G : BondGraph V E) (A : Finset V) :
    hV G * A.card ≤ (vertexBoundary G A).ncard := by
  by_cases hA : A.Nonempty
  · have hb : BddBelow {r : ℝ | ∃ B : Finset V, B.Nonempty ∧
        r = (vertexBoundary G B).ncard / (B.card : ℝ)} := by
      refine ⟨0, ?_⟩
      rintro _ ⟨B,_,rfl⟩
      positivity
    have hh : hV G ≤ (vertexBoundary G A).ncard / (A.card : ℝ) :=
      csInf_le hb ⟨A,hA,rfl⟩
    exact (le_div_iff₀ (by exact_mod_cast hA.card_pos)).mp hh
  · simp [Finset.not_nonempty_iff_eq_empty.mp hA]

theorem finite_vertexBoundary (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : (vertexBoundary G A).Finite := by
  apply (A.finite_toSet.biUnion (fun x _ => finite_neighbors hloc x)).subset
  rintro y ⟨_,x,hx,hxy⟩
  exact Set.mem_iUnion.mpr ⟨x,Set.mem_iUnion.mpr ⟨hx,hxy⟩⟩

noncomputable def neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Finset V := (finite_neighbors hloc x).toFinset

@[simp] theorem mem_neighbors (G : BondGraph V E) (hloc : LocallyFinite G) (x y : V) :
    y ∈ neighbors G hloc x ↔ Adj G x y := by simp [neighbors]

noncomputable def neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : Finset V := S ∪ S.biUnion (neighbors G hloc)

theorem subset_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) : S ⊆ neighborClosure G hloc S := Finset.subset_union_left

theorem neighbor_mem_neighborClosure (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hxy : Adj G x y) :
    y ∈ neighborClosure G hloc S := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,hx,(mem_neighbors ..).mpr hxy⟩)

noncomputable def finiteAdjPairs (G : BondGraph V E) (K : Finset V) : Finset (V × V) :=
  (K ×ˢ K).filter (fun e => Adj G e.1 e.2)

@[simp] theorem mem_finiteAdjPairs (G : BondGraph V E) (K : Finset V) (e : V × V) :
    e ∈ finiteAdjPairs G K ↔ e.1 ∈ K ∧ e.2 ∈ K ∧ Adj G e.1 e.2 := by
  simp [finiteAdjPairs,and_assoc]

theorem adj_symm (G : BondGraph V E) {x y : V} (h : Adj G x y) : Adj G y x := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.trans (Sym2.eq_swap)⟩

theorem sum_swap_finiteAdjPairs (G : BondGraph V E) (K : Finset V)
    (f : V × V → ℝ) :
    ∑ e ∈ finiteAdjPairs G K, f e.swap = ∑ e ∈ finiteAdjPairs G K, f e := by
  apply Finset.sum_bij (fun e _ => e.swap)
  · intro e he
    rw [mem_finiteAdjPairs] at he ⊢
    exact ⟨he.2.1,he.1,adj_symm G he.2.2⟩
  · intro a _ b _ h
    exact Prod.swap_injective h
  · intro b hb
    refine ⟨b.swap,?_,Prod.swap_swap b⟩
    rw [mem_finiteAdjPairs] at hb ⊢
    exact ⟨hb.2.1,hb.1,adj_symm G hb.2.2⟩
  · intros; rfl

 
theorem finiteAdjPairs_cut_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (S A : Finset V) (hAS : A ⊆ S) :
    (2 * hV G) * A.card ≤ ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S),
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  let R := P.filter (fun e => e.1 ∈ A ∧ e.2 ∉ A)
  have hs : (finite_vertexBoundary G hloc A).toFinset ⊆ R.image Prod.snd := by
    intro y hy
    have hy' : y ∈ vertexBoundary G A := by simpa using hy
    obtain ⟨hyA,x,hx,hxy⟩ := hy'
    apply Finset.mem_image.mpr
    refine ⟨(x,y),Finset.mem_filter.mpr ⟨?_,hx,hyA⟩,rfl⟩
    exact (mem_finiteAdjPairs G K (x,y)).mpr
      ⟨subset_neighborClosure G hloc S (hAS hx),
        neighbor_mem_neighborClosure G hloc S (hAS hx) hxy,hxy⟩
  have hc : (vertexBoundary G A).ncard ≤ R.card := by
    rw [Set.ncard_eq_toFinset_card (vertexBoundary G A) (finite_vertexBoundary G hloc A)]
    exact (Finset.card_le_card hs).trans (Finset.card_image_le)
  have hcross : hV G * A.card ≤ ∑ e ∈ P,
      if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    rw [Finset.sum_boole]
    exact (hV_mul_card_le G A).trans (by exact_mod_cast hc)
  have hsplit : ∑ e ∈ P,
      |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
      2 * ∑ e ∈ P, if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0 := by
    have ht (e : V × V) :
        |(if e.1 ∈ A then (1:ℝ) else 0) - (if e.2 ∈ A then (1:ℝ) else 0)| =
        (if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0) +
        (if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) := by
      by_cases h₁ : e.1 ∈ A <;> by_cases h₂ : e.2 ∈ A <;> simp [h₁,h₂]
    simp_rw [ht]
    rw [Finset.sum_add_distrib]
    have he := sum_swap_finiteAdjPairs G K
      (fun e => if e.1 ∈ A ∧ e.2 ∉ A then (1:ℝ) else 0)
    change (∑ e ∈ P, if e.2 ∈ A ∧ e.1 ∉ A then (1:ℝ) else 0) = _ at he
    rw [he]
    ring
  change _ ≤ ∑ e ∈ P, _
  rw [hsplit]
  nlinarith

 
theorem bondGraph_coarea (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (2 * hV G) * ∑ x ∈ S, f x ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), |f e.1 - f e.2| :=
  finite_coarea_lower_bound S _ f hf hout _
    (fun A hAS => finiteAdjPairs_cut_bound G hloc S A hAS)

theorem neighbors_card_le_degree (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    (neighbors G hloc x).card ≤ degree G x := by
  let : Fintype (Step G x) := (finite_steps G hloc x).fintype
  let p : Step G x → {y // y ∈ neighbors G hloc x} :=
    fun d => ⟨d.val.2, (mem_neighbors G hloc x d.val.2).mpr ⟨d.val.1,d.property⟩⟩
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨e,he⟩ := (mem_neighbors G hloc x y.val).mp y.property
    exact ⟨⟨(e,y.val),he⟩,Subtype.ext rfl⟩
  simpa only [degree,Nat.card_eq_fintype_card,Fintype.card_coe] using
    Fintype.card_le_of_surjective p hp

theorem finiteAdjPairs_source_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (K : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ e ∈ finiteAdjPairs G K, f e.1 ≤ (D:ℝ) * ∑ x ∈ K, f x := by
  rw [Finset.mul_sum]
  simp only [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_le_sum
  intro x _
  have hc : (K.filter (fun y => Adj G x y)).card ≤ D := by
    apply (Finset.card_le_card ?_).trans ((neighbors_card_le_degree G hloc x).trans (hD x))
    intro y hy
    exact (mem_neighbors G hloc x y).mpr (Finset.mem_filter.mp hy).2
  calc
    (∑ y ∈ K, if Adj G x y then f x else 0) =
        ((K.filter (fun y => Adj G x y)).card:ℝ) * f x := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (D:ℝ) * f x := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf x)

theorem finiteAdjPairs_square_sum_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (S : Finset V) (f : V → ℝ)
    (hout : ∀ x ∉ S, f x = 0) :
    ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1 + f e.2)^2 ≤
      4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
  let K := neighborClosure G hloc S
  let P := finiteAdjPairs G K
  have hs : ∑ x ∈ K, (f x)^2 = ∑ x ∈ S, (f x)^2 := by
    symm
    apply Finset.sum_subset (subset_neighborClosure G hloc S)
    intro x _ hx
    simp [hout x hx]
  have hfirst := finiteAdjPairs_source_sum_le G hloc D hD K (fun x => (f x)^2) (fun _ => sq_nonneg _)
  rw [hs] at hfirst
  have hsecond := sum_swap_finiteAdjPairs G K (fun e => (f e.1)^2)
  change (∑ e ∈ P, (f e.2)^2) = ∑ e ∈ P, (f e.1)^2 at hsecond
  calc
    (∑ e ∈ P, (f e.1 + f e.2)^2) ≤ ∑ e ∈ P, (2*(f e.1)^2+2*(f e.2)^2) := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith [sq_nonneg (f e.1 - f e.2)]
    _ = 4 * ∑ e ∈ P, (f e.1)^2 := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hsecond]
      ring
    _ ≤ 4 * (D:ℝ) * ∑ x ∈ S, (f x)^2 := by
      nlinarith

 

theorem bondGraph_cheeger_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hD : ∀ x, degree G x ≤ D)
    (S : Finset V) (f : V → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hout : ∀ x ∉ S, f x = 0) :
    (hV G)^2 * ∑ x ∈ S, (f x)^2 ≤
      (D:ℝ) * ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  let N := ∑ x ∈ S, (f x)^2
  let E := ∑ e ∈ P, (f e.1-f e.2)^2
  have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := bondGraph_coarea G hloc S (fun x => (f x)^2)
    (fun _ => sq_nonneg _) (fun x hx => by rw [hout x hx]; norm_num)
  have ht (e : V × V) : |(f e.1)^2-(f e.2)^2| = |f e.1-f e.2| * (f e.1+f e.2) := by
    rw [show (f e.1)^2-(f e.2)^2 = (f e.1-f e.2)*(f e.1+f e.2) by ring,
      abs_mul,abs_of_nonneg (add_nonneg (hf _) (hf _))]
  simp_rw [ht] at hc
  have hc' : ((2*hV G)*N)^2 ≤
      (∑ e ∈ P, |f e.1-f e.2| * (f e.1+f e.2))^2 := by
    exact sq_le_sq₀ (by positivity) (Finset.sum_nonneg (fun e _ => mul_nonneg (abs_nonneg _)
      (add_nonneg (hf _) (hf _)))) |>.mpr hc
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq P
    (fun e => |f e.1-f e.2|) (fun e => f e.1+f e.2)
  simp only [sq_abs] at hcs
  have hbound := finiteAdjPairs_square_sum_le G hloc D hD S f hout
  have hall : ((2*hV G)*N)^2 ≤ E*(4*(D:ℝ)*N) :=
    (hc'.trans hcs).trans (mul_le_mul_of_nonneg_left hbound hE)
  change (hV G)^2*N ≤ (D:ℝ)*E
  rcases hN.eq_or_lt with hzero | hpos
  · rw [←hzero,mul_zero]
    positivity
  · apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4*N)).mp
    nlinarith [hall]

end IsoperimetricEnergy

section FiniteQuadraticForms
attribute [local instance] Classical.propDecidable

@[simp] theorem finiteEmbedding_inner_left (f : V →₀ ℂ) (g : Hilbert V) :
    inner ℂ (finiteEmbedding f) g = ∑ x ∈ f.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_left, mul_comm]

@[simp] theorem finiteEmbedding_inner_right (f : Hilbert V) (g : V →₀ ℂ) :
    inner ℂ f (finiteEmbedding g) = ∑ x ∈ g.support, star (f x) * g x := by
  simp [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    lp.inner_single_right, mul_comm]

@[simp] theorem finiteEmbedding_norm_sq (f : V →₀ ℂ) :
    ‖finiteEmbedding f‖^2 = ∑ x ∈ f.support, ‖f x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [finiteEmbedding_inner_left]
  simp only [map_sum, finiteEmbedding_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

 theorem kernel_finiteEmbedding (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (f : V →₀ ℂ) (x : V) :
    A (finiteEmbedding f) x = ∑ y ∈ f.support, f y * (U x y : ℂ) := by
  simp only [finiteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul]
  change (∑ y ∈ f.support, f y • A (lp.single 2 y (1 : ℂ))) x = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    hA, smul_eq_mul]

 theorem symmetric_of_symmetric_kernel (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, U x y = U y x) : A.toLinearMap.IsSymmetric := by
  apply finiteEmbedding_dense.induction_on₂
    (p := fun f g => inner ℂ (A f) g = inner ℂ f (A g))
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro f g
    simp only [finiteEmbedding_inner_left, finiteEmbedding_inner_right,
      kernel_finiteEmbedding A U hA, map_sum, map_mul, RCLike.star_def,
      Complex.conj_ofReal]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hU y x]
    ring

 theorem norm_le_of_finite_quadratic (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : A.toLinearMap.IsSymmetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : V →₀ ℂ,
      |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
        C * ‖finiteEmbedding f‖^2) : ‖A‖ ≤ C := by
  have hall (f : Hilbert V) : |(inner ℂ (A f) f).re| ≤ C * ‖f‖^2 := by
    exact finiteEmbedding_dense.induction_on f
      (p := fun g => |(inner ℂ (A g) g).re| ≤ C * ‖g‖^2)
      (isClosed_le (by fun_prop) (by fun_prop)) h
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp [hf, hC]
  · rw [ContinuousLinearMap.rayleighQuotient, abs_div, abs_sq]
    exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hf))).mpr (hall f)

 theorem abs_inner_kernel_finite_le (A : Hilbert V →L[ℂ] Hilbert V)
    (U : V → V → ℝ) (hA : ∀ x y, A (lp.single 2 y (1 : ℂ)) x = (U x y : ℂ))
    (hU : ∀ x y, 0 ≤ U x y) (f : V →₀ ℂ) :
    |(inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f)).re| ≤
      ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖ * ‖f y‖ * U x y := by
  change |RCLike.re (inner ℂ (A (finiteEmbedding f)) (finiteEmbedding f))| ≤ _
  rw [inner_re_symm]
  apply (Complex.abs_re_le_norm _).trans
  rw [finiteEmbedding_inner_left]
  simp_rw [kernel_finiteEmbedding A U hA, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y _
  simp [abs_of_nonneg (hU x y), mul_assoc]

end FiniteQuadraticForms

section SymmetricWalk
attribute [local instance] Classical.propDecidable

 

noncomputable def walkKernel (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : ℝ :=
  (if x = y then 1 - a * (neighbors G hloc x).card else 0) +
    (if Adj G x y then a else 0)

 theorem walkKernel_symmetric (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x y : V) : walkKernel G hloc a x y = walkKernel G hloc a y x := by
  have ha : Adj G x y ↔ Adj G y x := ⟨adj_symm G,adj_symm G⟩
  by_cases h : x = y
  · subst y; rfl
  · simp [walkKernel,h,Ne.symm h,ha]

 theorem walkKernel_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x y : V) : 0 ≤ walkKernel G hloc a x y := by
  have hn : ((neighbors G hloc x).card : ℝ) ≤ D := by
    exact_mod_cast (neighbors_card_le_degree G hloc x).trans (hD x)
  have hh : 0 ≤ 1-a*(neighbors G hloc x).card := by nlinarith
  unfold walkKernel
  split_ifs <;> positivity

 theorem walkKernel_row_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (x : V) :
    ∑ y ∈ insert x (neighbors G hloc x), walkKernel G hloc a x y = 1 := by
  let N := neighbors G hloc x
  have hf : (insert x N).filter (fun y => Adj G x y) = N := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert]
    rw [mem_neighbors]
    exact ⟨fun h => h.2, fun h => ⟨Or.inr h,h⟩⟩
  simp only [walkKernel, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_insert_self,ite_true]
  rw [← Finset.sum_filter,hf]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [N]
  ring

 theorem walkKernel_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1)
    (x : V) (S : Finset V) : ∑ y ∈ S, walkKernel G hloc a x y ≤ 1 := by
  let N := insert x (neighbors G hloc x)
  calc
    ∑ y ∈ S, walkKernel G hloc a x y ≤ ∑ y ∈ S ∪ N, walkKernel G hloc a x y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun y _ _ => walkKernel_nonneg G hloc D hD a ha haD x y)
    _ = ∑ y ∈ N, walkKernel G hloc a x y := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro y _ hy
      have hxy : x ≠ y := by intro h; subst y; exact hy (by simp [N])
      have hna : ¬ Adj G x y := by intro h; exact hy (by simp [N,h])
      simp [walkKernel,hxy,hna]
    _ = 1 := walkKernel_row_sum G hloc a x

 theorem exists_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (D : ℕ) (hD : ∀ x, degree G x ≤ D) (a : ℝ) (ha : 0 ≤ a) (haD : a*D ≤ 1) :
    ∃ P : Hilbert V →L[ℂ] Hilbert V, ‖P‖ ≤ 1 ∧
      P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1 : ℂ)) x = (walkKernel G hloc a x y : ℂ) := by
  obtain ⟨P,hP,hK⟩ := exists_operator_of_row_column_bound (walkKernel G hloc a) 1
    zero_le_one (walkKernel_nonneg G hloc D hD a ha haD)
    (walkKernel_row_bound G hloc D hD a ha haD) (by
      intro y S
      simp_rw [walkKernel_symmetric G hloc a]
      exact walkKernel_row_bound G hloc D hD a ha haD y S)
  exact ⟨P,hP,symmetric_of_symmetric_kernel P _ hK (walkKernel_symmetric G hloc a),hK⟩

 theorem finiteAdjPairs_sum (G : BondGraph V E) (K : Finset V) (f : V × V → ℝ) :
    (∑ e ∈ finiteAdjPairs G K, f e) =
      ∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f (x,y) else 0 := by
  simp [finiteAdjPairs,Finset.sum_filter,Finset.sum_product]

 theorem finiteAdjPairs_source_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1) =
      ∑ x ∈ S, ((neighbors G hloc x).card : ℝ) * f x := by
  let K := neighborClosure G hloc S
  rw [finiteAdjPairs_sum]
  have he (x : V) (hx : x ∈ S) :
      K.filter (fun y => Adj G x y) = neighbors G hloc x := by
    ext y
    simp only [Finset.mem_filter,mem_neighbors]
    exact ⟨fun h => h.2,fun h => ⟨neighbor_mem_neighborClosure G hloc S hx h,h⟩⟩
  have hout' : ∀ x ∉ S, (∑ y ∈ K, if Adj G x y then f x else 0) = 0 := by
    intro x hx; simp [hout x hx]
  change (∑ x ∈ K, ∑ y ∈ K, if Adj G x y then f x else 0) = _
  rw [← Finset.sum_subset (subset_neighborClosure G hloc S)
    (fun x _ hx => hout' x hx)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter,he x hx]
  simp

 theorem finiteAdjPairs_product_sum (G : BondGraph V E) (hloc : LocallyFinite G)
    (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), f e.1 * f e.2) =
      ∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0 := by
  rw [finiteAdjPairs_sum]
  have hs := subset_neighborClosure G hloc S
  calc
    _ = ∑ x ∈ S, ∑ y ∈ neighborClosure G hloc S,
        if Adj G x y then f x*f y else 0 := by
      symm; apply Finset.sum_subset hs
      intro x _ hx; simp [hout x hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      symm; apply Finset.sum_subset hs
      intro y _ hy; simp [hout y hy]

 theorem walkKernel_energy (G : BondGraph V E) (hloc : LocallyFinite G)
    (a : ℝ) (S : Finset V) (f : V → ℝ) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
      ∑ x ∈ S, (f x)^2 - a/2 *
        ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 := by
  let P := finiteAdjPairs G (neighborClosure G hloc S)
  have henergy : (∑ e ∈ P, (f e.1-f e.2)^2) =
      2*(∑ x ∈ S, (neighbors G hloc x).card * (f x)^2) -
      2*(∑ x ∈ S, ∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    have hs := sum_swap_finiteAdjPairs G (neighborClosure G hloc S)
      (fun e => (f e.1)^2)
    change (∑ e ∈ P,(f e.2)^2) = (∑ e ∈ P,(f e.1)^2) at hs
    have hfirst := finiteAdjPairs_source_sum G hloc S (fun x => (f x)^2)
      (fun x hx => by rw [hout x hx]; norm_num)
    calc
      _ = (∑ e ∈ P, (f e.1)^2) + (∑ e ∈ P,(f e.2)^2) -
          2*(∑ e ∈ P,f e.1*f e.2) := by
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
        simp_rw [mul_assoc,← Finset.mul_sum]
        ring
      _ = _ := by rw [hs,hfirst,finiteAdjPairs_product_sum G hloc S f hout]; ring
  rw [henergy]
  have hpoint (x : V) (hx : x ∈ S) :
      (∑ y ∈ S, f x*f y*walkKernel G hloc a x y) =
        (f x)^2 - a*((neighbors G hloc x).card*(f x)^2) +
         a*(∑ y ∈ S, if Adj G x y then f x*f y else 0) := by
    simp only [walkKernel,mul_add,Finset.sum_add_distrib]
    have hi : (∑ y ∈ S, f x*f y*(if x=y then 1-a*(neighbors G hloc x).card else 0)) =
        (f x)^2*(1-a*(neighbors G hloc x).card) := by
      simp_rw [mul_ite,mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [hx,ite_true]
      ring
    rw [hi,Finset.mul_sum]
    have hj : (∑ y ∈ S, f x*f y*(if Adj G x y then a else 0)) =
        ∑ y ∈ S, a*(if Adj G x y then f x*f y else 0) := by
      apply Finset.sum_congr rfl
      intro y _
      split_ifs <;> ring
    rw [hj]
    ring
  simp_rw [Finset.sum_congr rfl hpoint,Finset.sum_add_distrib,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

 

theorem walkKernel_quadratic_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 ≤ a) (S : Finset V) (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hout : ∀ x ∉ S, f x = 0) :
    (∑ x ∈ S, ∑ y ∈ S, f x*f y*walkKernel G hloc a x y) ≤
      (1 - a*(hV G)^2/(2*D)) * ∑ x ∈ S, (f x)^2 := by
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hc := bondGraph_cheeger_energy G hloc hh D hD S f hf hout
  have he : ((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ) ≤
      ∑ e ∈ finiteAdjPairs G (neighborClosure G hloc S), (f e.1-f e.2)^2 :=
    (div_le_iff₀ hDp').mpr (by simpa only [mul_comm] using hc)
  rw [walkKernel_energy G hloc a S f hout]
  calc
    _ ≤ (∑ x ∈ S, (f x)^2) - a/2 *
        (((hV G)^2 * ∑ x ∈ S, (f x)^2)/(D:ℝ)) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left he (by positivity)) _
    _ = _ := by ring

 

theorem walk_operator_norm_lt_one (G : BondGraph V E) (hloc : LocallyFinite G)
    (hh : 0 < hV G) (D : ℕ) (hDp : 0 < D) (hD : ∀ x, degree G x ≤ D)
    (a : ℝ) (ha : 0 < a) (haD : a*D ≤ 1)
    (P : Hilbert V →L[ℂ] Hilbert V)
    (hP : ∀ x y, P (lp.single 2 y (1:ℂ)) x = (walkKernel G hloc a x y : ℂ)) :
    ‖P‖ < 1 := by
  let C := max 0 (1-a*(hV G)^2/(2*D))
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have hC : 0 ≤ C := le_max_left _ _
  have hC1 : C < 1 := by
    apply max_lt (by norm_num)
    have : 0 < a*(hV G)^2/(2*D) := by positivity
    linarith
  have hn : ‖P‖ ≤ C := by
    apply norm_le_of_finite_quadratic P
      (symmetric_of_symmetric_kernel P _ hP (walkKernel_symmetric G hloc a)) C hC
    intro f
    calc
      _ ≤ ∑ x ∈ f.support, ∑ y ∈ f.support, ‖f x‖*‖f y‖*walkKernel G hloc a x y :=
        abs_inner_kernel_finite_le P _ hP (walkKernel_nonneg G hloc D hD a ha.le haD) f
      _ ≤ (1-a*(hV G)^2/(2*D)) * ∑ x ∈ f.support, ‖f x‖^2 :=
        walkKernel_quadratic_bound G hloc hh D hDp hD a ha.le f.support
          (fun x => ‖f x‖) (fun _ => norm_nonneg _) (by
            intro x hx; simp [Finsupp.notMem_support_iff.mp hx])
      _ ≤ C * ∑ x ∈ f.support, ‖f x‖^2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      _ = C * ‖finiteEmbedding f‖^2 := by rw [finiteEmbedding_norm_sq]
  exact hn.trans_lt hC1

 

theorem exists_strict_walk_operator (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) :
    ∃ (D : ℕ) (P : Hilbert V →L[ℂ] Hilbert V), 0 < D ∧
      (∀ x, degree G x ≤ D) ∧ ‖P‖ < 1 ∧ P.toLinearMap.IsSymmetric ∧
      ∀ x y, P (lp.single 2 y (1:ℂ)) x =
        (walkKernel G hloc (1/(2*(D:ℝ))) x y : ℂ) := by
  obtain ⟨D,hDp,hD⟩ := exists_degree_bound G hqt
  have hDp' : 0 < (D:ℝ) := by exact_mod_cast hDp
  have ha : 0 < (1:ℝ)/(2*D) := by positivity
  have haD : (1:ℝ)/(2*D)*D ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨P,_,hPs,hP⟩ := exists_walk_operator G hloc D hD _ ha.le haD
  exact ⟨D,P,hDp,hD,walk_operator_norm_lt_one G hloc hh D hDp hD _ ha haD P hP,hPs,hP⟩

end SymmetricWalk

section PositiveConnectionKernel
open scoped ComplexOrder Matrix
attribute [local instance] Classical.propDecidable

 

theorem equivalenceMatrix_posSemidef {α : Type*} [Fintype α] (R : Setoid α) :
    Matrix.PosSemidef (fun x y => if R.r x y then (1:ℂ) else 0) := by
  classical
  let : Fintype (Quotient R) := Fintype.ofFinite (Quotient R)
  let J : Matrix (Quotient R) α ℂ := fun q x => if q = Quotient.mk R x then 1 else 0
  have hJ : Jᴴ * J = (fun x y => if R.r x y then (1:ℂ) else 0) := by
    ext x y
    change (∑ q : Quotient R, star (J q x) * J q y) = _
    have hr : R.r y x ↔ R.r x y := ⟨R.symm, R.symm⟩
    simp [J, Quotient.eq, hr]
  rw [← hJ]
  exact Matrix.posSemidef_conjTranspose_mul_self J

theorem connection_quadratic_nonneg (G : BondGraph V E) (ω : Set E)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y := by
  classical
  let R : Setoid S := ⟨fun x y => Conn G ω x y,
    ⟨fun x => conn_refl G ω x, fun h => conn_symm G ω h, fun h h' => conn_trans G ω h h'⟩⟩
  have h := (equivalenceMatrix_posSemidef R).dotProduct_mulVec_nonneg
    (fun x : S => f x)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply] at h
  change 0 ≤ ∑ x : S, ∑ y : S,
    star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) at h
  have he : (∑ x : S, ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y)) =
      ∑ x ∈ S, ∑ y ∈ S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y) := by
    rw [Finset.sum_coe_sort S (fun x => ∑ y : S,
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))]
    apply Finset.sum_congr rfl
    intro x _
    exact Finset.sum_coe_sort S (fun y =>
      star (f x) * ((if Conn G ω x y then (1:ℂ) else 0) * f y))
  rw [he] at h
  simpa only [mul_assoc] using h

variable [Countable V] [Countable E]

theorem conn_indicator_integrable (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Integrable (fun ω => if Conn G ω x y then (1:ℂ) else 0) (law p) := by
  change Integrable ({ω | Conn G ω x y}.indicator (fun _ => (1:ℂ))) (law p)
  exact (integrable_const (1:ℂ)).indicator (measurableSet_conn G x y)

theorem twoPoint_eq_integral (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (twoPoint G p x y : ℂ) =
      ∫ ω, (if Conn G ω x y then (1:ℂ) else 0) ∂law p := by
  simpa only [Set.indicator, Set.mem_ofPred_eq, Measure.real, twoPoint,
    Complex.real_smul, mul_one] using
    (integral_indicator_const (μ := law p) (1:ℂ) (measurableSet_conn G x y)).symm

theorem twoPoint_quadratic_nonneg (G : BondGraph V E) (p : unitInterval)
    (S : Finset V) (f : V → ℂ) :
    0 ≤ ∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y := by
  have hi (x y : V) : Integrable
      (fun ω => star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y) (law p) :=
    ((conn_indicator_integrable G p x y).const_mul _).mul_const _
  have hsum : (∑ x ∈ S, ∑ y ∈ S, star (f x) * (twoPoint G p x y : ℂ) * f y) =
      ∫ ω, ∑ x ∈ S, ∑ y ∈ S,
        star (f x) * (if Conn G ω x y then (1:ℂ) else 0) * f y ∂law p := by
    rw [integral_finsetSum S (fun x _ => integrable_finsetSum S (fun y _ => hi x y))]
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum S (fun y _ => hi x y)]
    apply Finset.sum_congr rfl
    intro y _
    rw [integral_mul_const, integral_const_mul, twoPoint_eq_integral]
  rw [hsum]
  exact integral_nonneg (fun ω => connection_quadratic_nonneg G ω S f)

 

theorem HasKernel.isPositive (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) : A.IsPositive := by
  have hs : A.toLinearMap.IsSymmetric :=
    symmetric_of_symmetric_kernel A (twoPoint G p) (fun x y => hA x y) (twoPoint_symm G p)
  refine ⟨hs, ?_⟩
  intro f
  apply finiteEmbedding_dense.induction_on f
    (p := fun g => 0 ≤ (inner ℂ (A g) g).re)
  · exact isClosed_le continuous_const (by fun_prop)
  · intro g
    rw [show inner ℂ (A (finiteEmbedding g)) (finiteEmbedding g) =
      inner ℂ (finiteEmbedding g) (A (finiteEmbedding g)) from hs _ _, finiteEmbedding_inner_left]
    simp only [kernel_finiteEmbedding A (twoPoint G p) (fun x y => hA x y)]
    simp_rw [Finset.mul_sum]
    have h := twoPoint_quadratic_nonneg G p g.support g
    apply Complex.nonneg_iff.mp at h
    convert h.1 using 1
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring

end PositiveConnectionKernel

section InvariantOperatorTrace
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable
local instance spectralRealOperatorScalarTower :
    IsScalarTower ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_assoc scalar first second := by
    ext vector vertex
    rfl
local instance spectralRealOperatorSMulCommClass :
    SMulCommClass ℝ (Hilbert V →L[ℂ] Hilbert V) (Hilbert V →L[ℂ] Hilbert V) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm
local instance spectralNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
local instance spectralContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ
    (Hilbert V →L[ℂ] Hilbert V) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus (A := Hilbert V →L[ℂ] Hilbert V)
noncomputable def permuteHilbert (a : V ≃ V) : Hilbert V ≃ₗᵢ[ℂ] Hilbert V where
  toFun f := ⟨fun x => f (a.symm x), by
    apply memℓp_gen
    exact a.symm.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  invFun f := ⟨fun x => f (a x), by
    apply memℓp_gen
    exact a.summable_iff.mpr (lp.memℓp f |>.summable (by norm_num))⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact a.symm.tsum_eq (fun x => ‖f x‖ ^ (2:ℝ≥0∞).toReal)

@[simp] theorem permuteHilbert_apply (a : V ≃ V) (f : Hilbert V) (x : V) :
    permuteHilbert a f x = f (a.symm x) := rfl

@[simp] theorem permuteHilbert_single (a : V ≃ V) (x : V) (c : ℂ) :
    permuteHilbert a (lp.single 2 x c) = lp.single 2 (a x) c := by
  ext y
  simp only [permuteHilbert_apply, lp.coeFn_single]
  simp [Pi.single_apply, eq_comm, Equiv.eq_symm_apply]

noncomputable def matrixCoeff (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) : ℂ :=
  A (lp.single 2 y (1:ℂ)) x

@[simp] theorem matrixCoeff_eq_inner (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff A x y = inner ℂ (lp.single 2 x (1:ℂ)) (A (lp.single 2 y (1:ℂ))) := by
  simp [matrixCoeff,lp.inner_single_left]

theorem operator_kernel_hasSum (A : Hilbert V →L[ℂ] Hilbert V) (f : Hilbert V) (x : V) :
    HasSum (fun y => matrixCoeff A x y * f y) (A f x) := by
  have h := ((lp.evalCLM ℂ (fun _ : V => ℂ) 2 x).comp A).hasSum
    (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) f)
  change HasSum (fun y => A (lp.single 2 y (f y)) x) (A f x) at h
  have heq : (fun y : V => A (lp.single 2 y (f y)) x) =
      (fun y => matrixCoeff A x y * f y) := by
    funext y
    have he : lp.single (E := fun _ : V => ℂ) 2 y (f y) =
        f y • lp.single 2 y (1:ℂ) := by
      rw [← lp.single_smul]; simp
    simp [he, matrixCoeff, mul_comm]
  rw [heq] at h
  exact h

@[simp] theorem matrixCoeff_mul (A B : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (A*B) x y = ∑' z, matrixCoeff A x z * matrixCoeff B z y := by
  exact (operator_kernel_hasSum A (B (lp.single 2 y (1:ℂ))) x).tsum_eq.symm

@[simp] theorem matrixCoeff_adjoint (A : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (star A) x y = star (matrixCoeff A y x) := by
  rw [matrixCoeff_eq_inner, matrixCoeff_eq_inner]
  change inner ℂ _ ((ContinuousLinearMap.adjoint A) _) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  simpa only [RCLike.star_def] using
    (inner_conj_symm (A (lp.single 2 x (1:ℂ))) (lp.single 2 y (1:ℂ))).symm

 
theorem matrixCoeff_invariant_iff (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V) :
    (∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) ↔
      Commute A (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap := by
  constructor
  · intro h
    change A * (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap =
      (permuteHilbert a).toContinuousLinearEquiv.toContinuousLinearMap * A
    apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
    intro y
    apply ContinuousLinearMap.ext
    intro c
    ext x
    have hs : lp.single (E := fun _ : V => ℂ) 2 y c =
        c • lp.single 2 y (1:ℂ) := by rw [← lp.single_smul]; simp
    have hh := h (a.symm x) y
    simp only [Equiv.apply_symm_apply] at hh
    change A (permuteHilbert a (lp.single 2 y c)) x =
      permuteHilbert a (A (lp.single 2 y c)) x
    rw [hs]
    simp only [map_smul, permuteHilbert_single, lp.coeFn_smul, Pi.smul_apply,
      permuteHilbert_apply]
    change c * matrixCoeff A x (a y) = c * matrixCoeff A (a.symm x) y
    rw [hh]
  · intro h x y
    have hh := congrArg (fun F : Hilbert V →L[ℂ] Hilbert V =>
      F (lp.single 2 y (1:ℂ)) (a x)) h.eq
    simpa only [mul_apply_eq_comp, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, permuteHilbert_single, permuteHilbert_apply,
      Equiv.symm_apply_apply, matrixCoeff] using hh

 theorem matrixCoeff_sqrt_invariant (a : V ≃ V) (A : Hilbert V →L[ℂ] Hilbert V)
    (h : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y) :
    ∀ x y, matrixCoeff (CFC.sqrt A) (a x) (a y) = matrixCoeff (CFC.sqrt A) x y := by
  apply (matrixCoeff_invariant_iff a _).mpr
  rw [CFC.sqrt_eq_cfc]
  exact ((matrixCoeff_invariant_iff a A).mp h).cfc_nnreal NNReal.sqrt

 theorem matrixCoeff_mul_invariant (a : V ≃ V) (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y)
    (hB : ∀ x y, matrixCoeff B (a x) (a y) = matrixCoeff B x y) :
    ∀ x y, matrixCoeff (A*B) (a x) (a y) = matrixCoeff (A*B) x y := by
  intro x y
  simp only [matrixCoeff_mul]
  rw [← a.tsum_eq (fun z => matrixCoeff A (a x) z * matrixCoeff B z (a y))]
  simp only [hA,hB]

 theorem matrixCoeff_nonneg (A : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x : V) :
    0 ≤ matrixCoeff A x x := by
  rw [matrixCoeff_eq_inner]
  exact (ContinuousLinearMap.nonneg_iff_isPositive |>.mp hA).inner_nonneg_right _

 theorem matrixCoeff_mono {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) (x : V) :
    matrixCoeff A x x ≤ matrixCoeff B x x := by
  have hh := matrixCoeff_nonneg (B-A) (sub_nonneg.mpr h) x
  simpa only [matrixCoeff, sub_apply, lp.coeFn_sub,
    Pi.sub_apply, sub_nonneg] using hh

section RootTrace
variable {ι : Type*} [Fintype ι]
variable (root : ι → V) (weight : ι → ℝ)

noncomputable def rootTrace (A : Hilbert V →L[ℂ] Hilbert V) : ℂ :=
  ∑ i, (weight i : ℂ) * matrixCoeff A (root i) (root i)

@[simp] theorem rootTrace_add (A B : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (A+B) = rootTrace root weight A + rootTrace root weight B := by
  simp [rootTrace, matrixCoeff, add_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem rootTrace_smul (c : ℂ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = c * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, ← Finset.mul_sum, mul_left_comm]

theorem rootTrace_nonneg (hw : ∀ i, 0 ≤ weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) : 0 ≤ rootTrace root weight A := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by simpa using hw i)
    (matrixCoeff_nonneg A hA (root i))

theorem rootTrace_mono (hw : ∀ i, 0 ≤ weight i)
    {A B : Hilbert V →L[ℂ] Hilbert V} (h : A ≤ B) :
    rootTrace root weight A ≤ rootTrace root weight B := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (matrixCoeff_mono h (root i)) (by simpa using hw i)

@[simp] theorem rootTrace_one (hw : ∑ i, weight i = 1) :
    rootTrace root weight (1 : Hilbert V →L[ℂ] Hilbert V) = 1 := by
  simpa [rootTrace, matrixCoeff, lp.coeFn_single, ← Complex.ofReal_sum] using
    congrArg (fun t : ℝ => (t : ℂ)) hw

 
def KernelInvariant (Γ : Set (V ≃ V)) (A : Hilbert V →L[ℂ] Hilbert V) : Prop :=
  ∀ a ∈ Γ, ∀ x y, matrixCoeff A (a x) (a y) = matrixCoeff A x y

theorem KernelInvariant.mul {Γ : Set (V ≃ V)}
    {A B : Hilbert V →L[ℂ] Hilbert V}
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    KernelInvariant Γ (A*B) := by
  intro a ha
  exact matrixCoeff_mul_invariant a A B (hA a ha) (hB a ha)

theorem KernelInvariant.star {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (star A) := by
  intro a ha x y
  simp only [matrixCoeff_adjoint, hA a ha]

theorem KernelInvariant.sqrt {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) :
    KernelInvariant Γ (CFC.sqrt A) := by
  intro a ha
  exact matrixCoeff_sqrt_invariant a A (hA a ha)

 

def RootTransport (Γ : Set (V ≃ V)) : Prop :=
  ∀ m : V → V → ℂ,
    (∀ a ∈ Γ, ∀ x y, m (a x) (a y) = m x y) →
    (∀ x, Summable (m x)) → (∀ y, Summable (fun x => m x y)) →
    (∑ i, (weight i : ℂ) * ∑' y, m (root i) y) =
    (∑ i, (weight i : ℂ) * ∑' x, m x (root i))

theorem rootTrace_cyclic {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B) :
    rootTrace root weight (A*B) = rootTrace root weight (B*A) := by
  have ht := htr (fun x y => matrixCoeff A x y * matrixCoeff B y x)
    (by intro a ha x y; rw [hA a ha, hB a ha])
    (fun x => (operator_kernel_hasSum A (B (lp.single 2 x (1:ℂ))) x).summable)
    (fun y => by
      simpa only [matrixCoeff, mul_comm] using
        (operator_kernel_hasSum B (A (lp.single 2 y (1:ℂ))) y).summable)
  simpa only [rootTrace, matrixCoeff_mul, mul_comm] using ht

theorem rootTrace_diag_le {Γ : Set (V ≃ V)}
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (c : ℝ) (hc : 0 ≤ c)
    (hmin : ∀ i, 1 ≤ c * weight i)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : KernelInvariant Γ A)
    (hApos : 0 ≤ A) (x : V) :
    matrixCoeff A x x ≤ (c : ℂ) * rootTrace root weight A := by
  obtain ⟨i,a,ha,hax⟩ := hcov x
  have hi : (weight i : ℂ) * matrixCoeff A (root i) (root i) ≤
      rootTrace root weight A := by
    unfold rootTrace
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j => (weight j : ℂ) * matrixCoeff A (root j) (root j))
      (fun j _ => mul_nonneg (by simpa using hw j) (matrixCoeff_nonneg A hApos _))
      (Finset.mem_univ i)
  calc
    matrixCoeff A x x = matrixCoeff A (root i) (root i) := by
      rw [← hax, hA a ha]
    _ ≤ (c * weight i : ℝ) * matrixCoeff A (root i) (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1:ℂ) ≤ ((c * weight i : ℝ) : ℂ) by exact_mod_cast hmin i)
        (matrixCoeff_nonneg A hApos (root i))
    _ = (c : ℂ) * ((weight i : ℂ) * matrixCoeff A (root i) (root i)) := by
      push_cast; ring
    _ ≤ (c : ℂ) * rootTrace root weight A :=
      mul_le_mul_of_nonneg_left hi (by exact_mod_cast hc)

@[simp] theorem rootTrace_real_smul (c : ℝ) (A : Hilbert V →L[ℂ] Hilbert V) :
    rootTrace root weight (c • A) = (c : ℂ) * rootTrace root weight A := by
  simp [rootTrace, matrixCoeff, smul_apply, Complex.real_smul,
    ← Finset.mul_sum, mul_left_comm]

theorem rootTrace_positive_mul_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hBsa : IsSelfAdjoint B) :
    rootTrace root weight (B*A) ≤ (‖B‖ : ℂ) * rootTrace root weight A := by
  let S := CFC.sqrt A
  have hS : S*S = A := CFC.sqrt_mul_sqrt_self A hApos
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have hSI : KernelInvariant Γ S := hA.sqrt
  have hbound : S*B*S ≤ ‖B‖ • A := by
    convert (CStarAlgebra.star_left_conjugate_le_norm_smul (a := S) (b := B) hBsa) using 1
    · rw [hSstar]
    · rw [hSstar, hS]
      ext f x
      rfl
  calc
    rootTrace root weight (B*A) = rootTrace root weight (S*(B*S)) := by
      rw [rootTrace_cyclic root weight htr S (B*S) hSI (hB.mul hSI)]
      rw [mul_assoc, hS]
    _ = rootTrace root weight (S*B*S) := by rw [mul_assoc]
    _ ≤ rootTrace root weight (‖B‖ • A) := rootTrace_mono root weight hw hbound
    _ = (‖B‖ : ℂ) * rootTrace root weight A := rootTrace_real_smul root weight _ _

theorem rootTrace_conjugate_le {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ) (hw : ∀ i, 0 ≤ weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) :
    rootTrace root weight (B*A*star B) ≤ ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
  calc
    rootTrace root weight (B*A*star B) = rootTrace root weight (star B*(B*A)) :=
      rootTrace_cyclic root weight htr (B*A) (star B) (hB.mul hA) hB.star
    _ = rootTrace root weight ((star B*B)*A) := by rw [mul_assoc]
    _ ≤ (‖star B*B‖ : ℂ) * rootTrace root weight A :=
      rootTrace_positive_mul_le root weight htr hw A (star B*B) hA (hB.star.mul hB)
        hApos (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg B))
    _ = ((‖B‖ ^ 2 : ℝ) : ℂ) * rootTrace root weight A := by
      have hnorm := CStarRing.norm_star_mul_self (x := B)
      have hn : ‖star B * B‖ = ‖B‖ ^ 2 := by
        convert hnorm using 1; simp only [pow_two]
      rw [hn]

 theorem matrixCoeff_gram (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    matrixCoeff (L*star M) x y =
      inner ℂ (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ))) := by
  rw [matrixCoeff_eq_inner]
  change inner ℂ _ (L ((ContinuousLinearMap.adjoint M) _)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  rfl

 theorem matrixCoeff_gram_norm_sq_le
    (L M : Hilbert V →L[ℂ] Hilbert V) (x y : V) :
    ‖matrixCoeff (L*star M) x y‖ ^ 2 ≤
      (matrixCoeff (L*star L) x x).re * (matrixCoeff (M*star M) y y).re := by
  simp only [matrixCoeff_gram]
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
      (star L (lp.single 2 x (1:ℂ))) (star M (lp.single 2 y (1:ℂ)))
  rw [norm_inner_symm (star M (lp.single 2 y (1:ℂ)))] at h
  simpa only [pow_two, RCLike.re_to_complex] using h

 theorem matrixCoeff_positive_product_norm_sq_le
    (A B : Hilbert V →L[ℂ] Hilbert V) (hA : 0 ≤ A) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ^ 2 ≤
      (matrixCoeff (B*A*star B) x x).re * (matrixCoeff A y y).re := by
  let S := CFC.sqrt A
  have hSS : S*S = A := CFC.sqrt_mul_sqrt_self A hA
  have hSstar : star S = S := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  convert matrixCoeff_gram_norm_sq_le (B*S) S x y using 1 <;>
    simp only [star_mul, hSstar, mul_assoc, ← mul_assoc S S, hSS]

 

theorem matrixCoeff_smoothing {Γ : Set (V ≃ V)}
    (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A B : Hilbert V →L[ℂ] Hilbert V)
    (hA : KernelInvariant Γ A) (hB : KernelInvariant Γ B)
    (hApos : 0 ≤ A) (hdiag : ∀ y, matrixCoeff A y y = 1) (x y : V) :
    ‖matrixCoeff (B*A) x y‖ ≤ Real.sqrt c * ‖B‖ := by
  have htA : rootTrace root weight A = 1 := by
    simp only [rootTrace, hdiag, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  have hD : 0 ≤ B*A*star B := star_right_conjugate_nonneg hApos B
  have hi : KernelInvariant Γ (B*A*star B) := (hB.mul hA).mul hB.star
  have ht := rootTrace_conjugate_le root weight htr hw A B hA hB hApos
  rw [htA, mul_one] at ht
  have hd : matrixCoeff (B*A*star B) x x ≤ ((c * ‖B‖^2 : ℝ) : ℂ) := by
    calc
      _ ≤ (c : ℂ) * rootTrace root weight (B*A*star B) :=
        rootTrace_diag_le root weight hcov hw c hc hmin _ hi hD x
      _ ≤ (c : ℂ) * ((‖B‖^2 : ℝ) : ℂ) :=
        mul_le_mul_of_nonneg_left ht (by exact_mod_cast hc)
      _ = _ := by push_cast; rfl
  have hd' : (matrixCoeff (B*A*star B) x x).re ≤ c * ‖B‖^2 :=
    (Complex.le_def.mp hd).1
  have hs : ‖matrixCoeff (B*A) x y‖ ^ 2 ≤ c * ‖B‖ ^ 2 := by
    have hh := matrixCoeff_positive_product_norm_sq_le A B hApos x y
    rw [hdiag, Complex.one_re, mul_one] at hh
    exact hh.trans hd'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hc]

end RootTrace

end InvariantOperatorTrace

section InvariantPercolationOperators
open scoped ComplexOrder InnerProduct
attribute [local instance] Classical.propDecidable

 
def vertexAut (G : BondGraph V E) : Set (V ≃ V) := {a | ∃ b : E ≃ E, IsAut G a b}

theorem twoPoint_aut [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (h : IsAut G a b) (x y : V) :
    twoPoint G p (a x) (a y) = twoPoint G p x y := by
  have he : {ω | Conn G ω (a x) (a y)} =
      (fun ω => b ⁻¹' ω) ⁻¹' {ω | Conn G ω x y} := by
    ext ω
    exact (conn_aut_iff G h ω x y).symm
  unfold twoPoint
  rw [he, ← Measure.map_apply (measurable_set_preimage b)
    (measurableSet_conn G x y), law_map_preimage_equiv]

theorem HasKernel.invariant [Countable V] [Countable E] (G : BondGraph V E) (p : unitInterval)
    (A : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A) :
    KernelInvariant (vertexAut G) A := by
  rintro a ⟨b, hab⟩ x y
  change A (lp.single 2 (a y) (1:ℂ)) (a x) = A (lp.single 2 y (1:ℂ)) x
  rw [hA, hA, twoPoint_aut G p hab]

theorem KernelInvariant.one (Γ : Set (V ≃ V)) :
    KernelInvariant Γ (1 : Hilbert V →L[ℂ] Hilbert V) := by
  intro a _ x y
  simp only [matrixCoeff, one_apply_eq_self, lp.coeFn_single]
  simp [Pi.single_apply, a.injective.eq_iff]

theorem KernelInvariant.pow {Γ : Set (V ≃ V)}
    {A : Hilbert V →L[ℂ] Hilbert V} (hA : KernelInvariant Γ A) (n : ℕ) :
    KernelInvariant Γ (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using KernelInvariant.one Γ
  | succ n ih => simpa only [pow_succ] using ih.mul hA

 

theorem twoPoint_operator_smoothing [Countable V] [Countable E] [Nonempty V] {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hsum : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c * weight i)
    (A P : Hilbert V →L[ℂ] Hilbert V) (hA : HasKernel G p A)
    (hP : KernelInvariant (vertexAut G) P) (l : ℕ) (x y : V) :
    ‖matrixCoeff (P^l*A) x y‖ ≤ Real.sqrt c * ‖P‖^l := by
  have hdiag (y : V) : matrixCoeff A y y = 1 := by
    change A (lp.single 2 y (1:ℂ)) y = 1
    rw [hA y y, twoPoint_self, Complex.ofReal_one]
  have h := matrixCoeff_smoothing root weight htr hcov hw hsum c hc hmin A (P^l)
    (hA.invariant G p A) (hP.pow l) (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (hA.isPositive G p A)) hdiag x y
  have hn (n : ℕ) : ‖P^n‖ ≤ ‖P‖^n := by
    induction n with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_def] using (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Hilbert V))
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg P))
  exact h.trans (mul_le_mul_of_nonneg_left (hn l) (Real.sqrt_nonneg c))
end InvariantPercolationOperators

end Percolation

end OAI
