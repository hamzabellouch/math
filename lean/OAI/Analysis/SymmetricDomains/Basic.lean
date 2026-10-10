import Mathlib

namespace OAI


namespace Release061

abbrev Affine (n : ℕ) := Fin n → ℂ

def realCoordinates {n : ℕ} (z : Affine n) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun j => (z j).re) (fun j => (z j).im)

def IsAffineAlgebraic {n : ℕ} (V : Set (Affine n)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n) ℂ),
    V = {z | ∀ p ∈ P, MvPolynomial.eval z p = 0}

inductive IsSemialgebraic {n : ℕ} : Set (Affine n) → Prop
  | zero (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | MvPolynomial.eval (realCoordinates z) p = 0}
  | positive (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | 0 < MvPolynomial.eval (realCoordinates z) p}
  | compl {S : Set (Affine n)} : IsSemialgebraic S → IsSemialgebraic Sᶜ
  | union {S T : Set (Affine n)} :
      IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∪ T)

def HolomorphicOnSubset {n m : ℕ} (S : Set (Affine n)) (f : S → Affine m) : Prop :=
  ∀ p : S, ∃ W : Set (Affine n), IsOpen W ∧ (p : Affine n) ∈ W ∧
    ∃ F : Affine n → Affine m, AnalyticOnNhd ℂ F W ∧
      ∀ q : S, (q : Affine n) ∈ W → F q = f q

structure Biholomorph {n m : ℕ} (S : Set (Affine n)) (T : Set (Affine m)) where
  toHomeomorph : S ≃ₜ T
  holomorphic_toFun : HolomorphicOnSubset S (fun p => (toHomeomorph p : Affine m))
  holomorphic_invFun : HolomorphicOnSubset T (fun q => (toHomeomorph.symm q : Affine n))

def IsSmooth {n : ℕ} (S : Set (Affine n)) : Prop :=
  ∀ p : S, ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ (p : Affine n) ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

def IsBoundedSymmetricDomain {n : ℕ} (D : Set (Affine n)) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    ∀ p : D, ∃ σ : Biholomorph D D,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set D, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p

theorem IsAffineAlgebraic.isClosed {n : ℕ} {V : Set (Affine n)}
    (hV : IsAffineAlgebraic V) : IsClosed V := by
  obtain ⟨P, rfl⟩ := hV
  have heq : {z | ∀ p ∈ P, MvPolynomial.eval z p = 0} =
      ⋂ p ∈ P, {z | MvPolynomial.eval z p = 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter fun p _ => isClosed_eq p.continuous_eval continuous_const

theorem locallyCompact_of_relative_open {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) :
    LocallyCompactSpace U := by
  have hloc := hU.isLocallyClosed.image
    Topology.IsEmbedding.subtypeVal.isInducing
    (by simpa using hV.isClosed.isLocallyClosed)
  have heq : (Subtype.val : V → Affine n) ''
      ((Subtype.val : V → Affine n) ⁻¹' U) = U := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUV hx⟩, hx, rfl⟩
  rw [heq] at hloc
  exact hloc.locallyCompactSpace

theorem exists_compact_orbit_representatives
    {X Γ : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [Group Γ] [MulAction Γ X] [ContinuousConstSMul Γ X]
    [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ y ∈ K, ∃ γ : Γ, γ • y = x := by
  classical
  choose K hK hKn using fun x : X => exists_compact_mem_nhds x
  let q : X → Quotient (MulAction.orbitRel Γ X) := Quotient.mk _
  have hq : IsOpenMap q := MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel Γ X))) ⊆
      ⋃ x : X, q '' interior (K x) := by
    intro a _
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
    exact Set.mem_iUnion.mpr ⟨x, ⟨x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => q '' interior (K x)) (fun _ => hq _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, K x, s.finite_toSet.isCompact_biUnion (fun x _ => hK x), ?_⟩
  intro x
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ (q x)))
  obtain ⟨has, y, hy, hxy⟩ := Set.mem_iUnion.mp ha
  refine ⟨y, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
    ⟨has, interior_subset hy⟩⟩, ?_⟩
  exact MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.eq.mp hxy.symm))

theorem HolomorphicOnSubset.continuous {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m} (hf : HolomorphicOnSubset S f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨W, hWo, hpW, F, hF, hFeq⟩ := hf p
  apply ((hF _ hpW).continuousAt.comp continuousAt_subtype_val).congr
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hWo.mem_nhds hpW)] with q hq
  exact hFeq q hq

theorem HolomorphicOnSubset.comp {n m l : ℕ}
    {S : Set (Affine n)} {T : Set (Affine m)}
    {f : S → T} {g : T → Affine l}
    (hg : HolomorphicOnSubset T g)
    (hf : HolomorphicOnSubset S (fun p => (f p : Affine m))) :
    HolomorphicOnSubset S (g ∘ f) := by
  intro p
  obtain ⟨W, hWo, hpW, F, hF, hFeq⟩ := hf p
  obtain ⟨V, hVo, hpV, G, hG, hGeq⟩ := hg (f p)
  have hFp : F p = (f p : Affine m) := hFeq p hpW
  have hFV : F ⁻¹' V ∈ nhds (p : Affine n) :=
    (hF _ hpW).continuousAt.preimage_mem_nhds (by simpa [hFp] using hVo.mem_nhds hpV)
  obtain ⟨O, hOV, hOo, hpO⟩ := mem_nhds_iff.mp hFV
  refine ⟨W ∩ O, hWo.inter hOo, ⟨hpW, hpO⟩, G ∘ F,
    hG.comp (hF.mono Set.inter_subset_left) (fun x hx => hOV hx.2), ?_⟩
  intro q hq
  change G (F q) = g (f q)
  rw [hFeq q hq.1]
  apply hGeq
  simpa [hFeq q hq.1] using hOV hq.2

theorem holomorphicOnSubset_val {n : ℕ} (S : Set (Affine n)) :
    HolomorphicOnSubset S Subtype.val := by
  intro p
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, id,
    analyticOnNhd_id, fun _ _ => rfl⟩

namespace Biholomorph

noncomputable def refl {n : ℕ} (S : Set (Affine n)) : Biholomorph S S where
  toHomeomorph := Homeomorph.refl S
  holomorphic_toFun := holomorphicOnSubset_val S
  holomorphic_invFun := holomorphicOnSubset_val S

noncomputable def symm {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    (e : Biholomorph S T) : Biholomorph T S where
  toHomeomorph := e.toHomeomorph.symm
  holomorphic_toFun := e.holomorphic_invFun
  holomorphic_invFun := e.holomorphic_toFun

noncomputable def trans {n m l : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    {R : Set (Affine l)} (e : Biholomorph S T) (f : Biholomorph T R) :
    Biholomorph S R where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  holomorphic_toFun := f.holomorphic_toFun.comp e.holomorphic_toFun
  holomorphic_invFun := e.holomorphic_invFun.comp f.holomorphic_invFun

end Biholomorph

theorem analytic_coefficient_difference_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : E → ℂ} {R B : ℝ} (hR : 0 < R)
    (ha : DifferentiableOn ℂ a (Metric.ball 0 R))
    (hB : ∀ z ∈ Metric.ball (0 : E) R, ‖a z‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball (0 : E) R) :
    ‖a 0 - a z‖ ≤ (2 * B / R) * ‖z‖ := by
  have hzero : (0 : E) ∈ Metric.ball (0 : E) R := by simpa using hR
  have hmap : Set.MapsTo a (Metric.ball (0 : E) R) (Metric.closedBall (a 0) (2 * B)) := by
    intro w hw
    change dist (a w) (a 0) ≤ 2 * B
    calc
      dist (a w) (a 0) ≤ ‖a w‖ + ‖a 0‖ := dist_le_norm_add_norm _ _
      _ ≤ B + B := add_le_add (hB w hw) (hB 0 hzero)
      _ = 2 * B := by ring
  simpa [dist_eq_norm_sub, norm_sub_rev] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball ha hmap hz

theorem coalescing_root_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r : ℕ} {R B : ℝ} (hR : 0 < R)
    (a : Fin r → E → ℂ)
    (ha : ∀ j, DifferentiableOn ℂ (a j) (Metric.ball 0 R))
    (hab : ∀ j z, z ∈ Metric.ball (0 : E) R → ‖a j z‖ ≤ B)
    {z : E} (hz : z ∈ Metric.ball (0 : E) R) {v w : ℂ}
    (hv : ‖v‖ ≤ 1)
    (hroot : (v - w) ^ r = ∑ j : Fin r, (a j 0 - a j z) * v ^ (j : ℕ)) :
    ‖v - w‖ ^ r ≤ (r : ℝ) * (2 * B / R) * ‖z‖ := by
  calc
    ‖v - w‖ ^ r = ‖(v - w) ^ r‖ := (norm_pow _ _).symm
    _ = ‖∑ j : Fin r, (a j 0 - a j z) * v ^ (j : ℕ)‖ := congrArg norm hroot
    _ ≤ ∑ j : Fin r, ‖(a j 0 - a j z) * v ^ (j : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin r, (2 * B / R) * ‖z‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, norm_pow]
      calc
        ‖a j 0 - a j z‖ * ‖v‖ ^ (j : ℕ) ≤ ‖a j 0 - a j z‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv) (norm_nonneg _)
        _ ≤ (2 * B / R) * ‖z‖ := by
          simpa using analytic_coefficient_difference_bound hR (ha j) (hab j) hz
    _ = (r : ℝ) * (2 * B / R) * ‖z‖ := by simp [mul_assoc]

theorem equicontinuousAt_of_coalescing_polynomials
    {X E ι : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : X} {π : X → E} (hπ : ContinuousAt π p) (hπp : π p = 0)
    {r : ℕ} {R B : ℝ} (hR : 0 < R)
    (h : ι → X → ℂ) (a : ι → Fin r → E → ℂ)
    (ha : ∀ i j, DifferentiableOn ℂ (a i j) (Metric.ball 0 R))
    (hab : ∀ i j z, z ∈ Metric.ball (0 : E) R → ‖a i j z‖ ≤ B)
    (hh : ∀ i x, ‖h i x‖ ≤ 1)
    (hroot : ∀ i x, (h i x - h i p) ^ r =
      ∑ j : Fin r, (a i j 0 - a i j (π x)) * h i x ^ (j : ℕ)) :
    EquicontinuousAt h p := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have ht : Filter.Tendsto (fun x => (r : ℝ) * (2 * B / R) * ‖π x‖)
      (nhds p) (nhds 0) := by
    simpa [hπp] using (hπ.norm.const_mul ((r : ℝ) * (2 * B / R))).tendsto
  have he := (tendsto_order.mp ht).2 (ε ^ r) (pow_pos hε r)
  have hball : ∀ᶠ x in nhds p, π x ∈ Metric.ball (0 : E) R :=
    hπ.preimage_mem_nhds (by simpa [hπp] using Metric.ball_mem_nhds (π p) hR)
  filter_upwards [he, hball] with x hx hxπ i
  have hpow := (coalescing_root_bound hR (a i) (ha i) (hab i) hxπ
    (hh i x) (hroot i x)).trans_lt hx
  have hn := lt_of_pow_lt_pow_left₀ r hε.le hpow
  simpa [dist_eq_norm_sub, norm_sub_rev] using hn

end Release061

end OAI
