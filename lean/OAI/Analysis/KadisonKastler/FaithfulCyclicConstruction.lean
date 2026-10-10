import OAI.Analysis.KadisonKastler.CountableAmplificationNormal
import OAI.Analysis.KadisonKastler.ReducingRestriction
import OAI.Analysis.KadisonKastler.KaplanskyDensity
import OAI.Analysis.KadisonKastler.PublishedStandardRepresentation

namespace OAI

/-! # A faithful cyclic representation from a countable amplification

The weighted dense vector is separating for the diagonal action. Its
closed orbit gives a faithful cyclic restriction. Kaplansky density and
weak compactness of the original operator ball show that the restricted
image is already a von Neumann algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter TopologicalSpace
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [SeparableSpace H]

def countableDiagonalHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (CountableHilbertSum H →L[ℂ] CountableHilbertSum H) :=
  l2DiagonalHom.comp M.toStarSubalgebra.subtype

abbrev faithfulCyclicSpace (M : VonNeumannAlgebra H) :=
  vectorOrbitClosure (countableDiagonalHom M).range (denseSeparatingUnitVector (H := H))

def faithfulCyclicVector (M : VonNeumannAlgebra H) : faithfulCyclicSpace M :=
  ⟨denseSeparatingUnitVector, mem_vectorOrbitClosure _ _⟩

theorem norm_faithfulCyclicVector (M : VonNeumannAlgebra H) :
    ‖faithfulCyclicVector M‖ = 1 := norm_denseSeparatingUnitVector

instance faithfulCyclicSpace_nontrivial (M : VonNeumannAlgebra H) :
    Nontrivial (faithfulCyclicSpace M) :=
  nontrivial_of_ne (faithfulCyclicVector M) 0 (by
    intro h
    have hn := norm_faithfulCyclicVector M
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)

def faithfulCyclicHom (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) :=
  (reducingRestriction (faithfulCyclicSpace M) (countableDiagonalHom M).range
    (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)).comp
      (countableDiagonalHom M).rangeRestrict

omit [Nontrivial H] in
@[simp] theorem faithfulCyclicHom_apply (M : VonNeumannAlgebra H) (a : Algebra M)
    (x : faithfulCyclicSpace M) :
    (faithfulCyclicHom M a x : CountableHilbertSum H) = l2Diagonal a.val x :=
  reducingRestriction_coe_apply _ _
    (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)
    ((countableDiagonalHom M).rangeRestrict a) x

theorem faithfulCyclicHom_separating (M : VonNeumannAlgebra H) :
    Function.Injective (fun a : Algebra M => faithfulCyclicHom M a (faithfulCyclicVector M)) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply Subtype.ext
  apply denseSeparatingUnitVector_separating
  have he := congrArg (fun x : faithfulCyclicSpace M => (x : CountableHilbertSum H)) hab
  simp only [faithfulCyclicHom_apply] at he
  change l2Diagonal (a.val - b.val) (denseSeparatingUnitVector (H := H)) = 0
  change (l2DiagonalHom (E := H) (a.val - b.val)) _ = 0
  rw [map_sub]
  exact sub_eq_zero.mpr he

theorem faithfulCyclicHom_injective (M : VonNeumannAlgebra H) :
    Function.Injective (faithfulCyclicHom M) := by
  intro a b hab
  exact faithfulCyclicHom_separating M (congrArg (fun T => T (faithfulCyclicVector M)) hab)

theorem faithfulCyclicHom_norm (M : VonNeumannAlgebra H) (a : Algebra M) :
    ‖faithfulCyclicHom M a‖ = ‖a‖ := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) := {}
  exact NonUnitalStarAlgHom.norm_map (faithfulCyclicHom M) (faithfulCyclicHom_injective M) a

omit [Nontrivial H] in
theorem faithfulCyclicHom_cyclic (M : VonNeumannAlgebra H) :
    DenseRange (fun a : Algebra M => faithfulCyclicHom M a (faithfulCyclicVector M)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp y.property ε hε
  obtain ⟨a, ha⟩ := b.property
  refine ⟨faithfulCyclicHom M a (faithfulCyclicVector M), ⟨a, rfl⟩, ?_⟩
  change dist y.val
    (↑(faithfulCyclicHom M a (faithfulCyclicVector M)) : CountableHilbertSum H) < ε
  rw [faithfulCyclicHom_apply]
  change dist y.val (b.val (denseSeparatingUnitVector (H := H))) < ε at hb
  change l2Diagonal a.val = b.val at ha
  rwa [ha]

omit [Nontrivial H] in
theorem faithfulCyclicHom_tendsto_weak (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} (a : ι → Algebra M) (b : Algebra M) (C : ℝ)
    (hn : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hweak : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) (x y : faithfulCyclicSpace M) :
    Tendsto (fun i => inner ℂ y (faithfulCyclicHom M (a i) x)) l
      (𝓝 (inner ℂ y (faithfulCyclicHom M b x))) := by
  simpa only [Submodule.coe_inner, faithfulCyclicHom_apply] using
    l2Diagonal_tendsto_weak (fun i => (a i).val) b.val C hn hweak x.val y.val

def faithfulCyclicAlgebra (M : VonNeumannAlgebra H) :
    VonNeumannAlgebra (faithfulCyclicSpace M) :=
  generatedVonNeumannAlgebra (faithfulCyclicHom M).range

/-- The full unit ball of the generated algebra is already the restricted image. -/
theorem faithfulCyclicHom_surjective_unitBall (M : VonNeumannAlgebra H)
    (T : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M)
    (hT : T ∈ faithfulCyclicAlgebra M) (hnT : ‖T‖ ≤ 1) :
    ∃ a : Algebra M, ‖a‖ ≤ 1 ∧ faithfulCyclicHom M a = T := by
  classical
  let K := faithfulCyclicSpace M
  let ρ := faithfulCyclicHom M
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := ρ.range
  have hcomm : T ∈ Set.centralizer (Set.centralizer (A : Set (K →L[ℂ] K))) := by
    change T ∈ (generatedVonNeumannAlgebra A : Set _ ) at hT
    rwa [generatedVonNeumannAlgebra_coe] at hT
  obtain ⟨c, hc, hlim⟩ := publishedKaplanskyDensity.exists_weak_contraction_net A T hcomm hnT
  choose a ha using fun d => (c d).property
  have ha' (d : Finset K × ℕ) : ρ (a d) = (c d).val := ha d
  have hn (d : Finset K × ℕ) : ‖a d‖ ≤ 1 := by
    rw [← faithfulCyclicHom_norm M]
    change ‖ρ (a d)‖ ≤ 1
    rw [ha' d]
    exact hc d
  let ω : Ultrafilter (Finset K × ℕ) := Ultrafilter.of atTop
  obtain ⟨b, hb, hweak⟩ := exists_weak_operator_ultralimit ω
    (fun d => (a d).val) 1 zero_le_one hn
  let a₀ : Algebra M := ⟨b, weak_operator_limit_mem M a b hweak⟩
  refine ⟨a₀, hb, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have h₁ := faithfulCyclicHom_tendsto_weak M a a₀ 1
    (Eventually.of_forall hn) hweak x y
  have h₂ : Tendsto (fun d => inner ℂ y (ρ (a d) x)) (ω : Filter (Finset K × ℕ))
      (𝓝 (inner ℂ y (T x))) := by
    simpa only [ha'] using (hlim x y).mono_left (Ultrafilter.of_le atTop)
  exact tendsto_nhds_unique h₁ h₂

theorem faithfulCyclicHom_surjective (M : VonNeumannAlgebra H)
    (T : faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M)
    (hT : T ∈ faithfulCyclicAlgebra M) : ∃ a : Algebra M, faithfulCyclicHom M a = T := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (faithfulCyclicSpace M →L[ℂ] faithfulCyclicSpace M) := {}
  by_cases hzero : T = 0
  · exact ⟨0, by rw [map_zero, hzero]⟩
  have hn : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
  have hsmall : ‖(‖T‖ : ℂ)⁻¹ • T‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg T), inv_mul_cancel₀ hn]
  obtain ⟨a, _, ha⟩ := faithfulCyclicHom_surjective_unitBall M
    ((‖T‖ : ℂ)⁻¹ • T) ((faithfulCyclicAlgebra M).toStarSubalgebra.smul_mem hT _) hsmall
  refine ⟨(‖T‖ : ℂ) • a, ?_⟩
  calc
    faithfulCyclicHom M ((‖T‖ : ℂ) • a) =
        (‖T‖ : ℂ) • faithfulCyclicHom M a :=
      (faithfulCyclicHom M).toAlgHom.toLinearMap.map_smul _ _
    _ = T := by
      rw [ha, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn), one_smul]

def faithfulCyclicEquiv (M : VonNeumannAlgebra H) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (faithfulCyclicAlgebra M) := by
  let ρ : Algebra M →⋆ₐ[ℂ] Algebra (faithfulCyclicAlgebra M) :=
    (faithfulCyclicHom M).codRestrict (faithfulCyclicAlgebra M).toStarSubalgebra
      (fun a => subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩)
  apply StarAlgEquiv.ofBijective ρ
  constructor
  · intro a b h
    apply faithfulCyclicHom_injective M
    exact congrArg Subtype.val h
  · intro T
    obtain ⟨a, ha⟩ := faithfulCyclicHom_surjective M T.val T.property
    exact ⟨a, Subtype.ext ha⟩

@[simp] theorem faithfulCyclicEquiv_coe (M : VonNeumannAlgebra H) (a : Algebra M) :
    (faithfulCyclicEquiv M a).val = faithfulCyclicHom M a := rfl

theorem faithfulCyclicAlgebra_separating (M : VonNeumannAlgebra H) :
    Function.Injective (algebraVectorMap (faithfulCyclicAlgebra M) (faithfulCyclicVector M)) := by
  intro a b hab
  obtain ⟨a', ha⟩ := faithfulCyclicHom_surjective M a.val a.property
  obtain ⟨b', hb⟩ := faithfulCyclicHom_surjective M b.val b.property
  have h : faithfulCyclicHom M a' (faithfulCyclicVector M) =
      faithfulCyclicHom M b' (faithfulCyclicVector M) := by
    rw [ha, hb]
    exact hab
  have he : a' = b' := faithfulCyclicHom_separating M h
  apply Subtype.ext
  exact ha.symm.trans ((congrArg (faithfulCyclicHom M) he).trans hb)

/-- Blackadar's faithful cyclic representation input, proved for the required
separably acting case by an explicit countable amplification. -/
theorem publishedFaithfulCyclicRepresentation : PublishedFaithfulCyclicRepresentation.{u} := by
  intro H _ _ _ _ _ M
  refine ⟨{
    K := faithfulCyclicSpace M
    algebra := faithfulCyclicAlgebra M
    equiv := faithfulCyclicEquiv M
    vector := faithfulCyclicVector M
    unit_vector := norm_faithfulCyclicVector M
    cyclic := ?_
    separating := faithfulCyclicAlgebra_separating M }⟩
  apply (faithfulCyclicHom_cyclic M).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨faithfulCyclicHom M a, subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩⟩, rfl⟩

end

end KadisonKastler

end OAI
