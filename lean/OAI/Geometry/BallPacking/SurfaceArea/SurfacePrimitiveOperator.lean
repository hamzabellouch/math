import Mathlib
import OAI.Geometry.BallPacking.SurfaceArea.QuadricEndAnnuli

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open Set Function Manifold MeasureTheory
open scoped ContDiff Manifold Topology

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
  {I : Type*} [Fintype I] {K : Set M}

def surfaceCovectorOperator (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    (Ω : ManifoldTwoForm Plane M) : ManifoldOneForm Plane M :=
  ∑ i, (boxCovectorOperator (B i) ((fun x => ρ i x • Ω x) -
      chartMass (B i).center (fun x => ρ i x • Ω x) • (D.bump i).form) +
    chartMass (B i).center (fun x => ρ i x • Ω x) • D.primitive i)

def surfaceCovectorSupport (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (D : SurfaceMassTransferData B B₀) : Set M :=
  ⋃ i, (B i).compactCarrier ∪ D.supportSet i

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem surfaceCovectorSupport_compact (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (D : SurfaceMassTransferData B B₀) : IsCompact (surfaceCovectorSupport B B₀ D) := by
  apply isCompact_iUnion
  intro i
  exact (B i).isCompact_compactCarrier.union (D.compact_supportSet i)

theorem surfaceCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (B₀ : SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u) (hz : ∀ p x, x ∉ K → Ω p x=0)
    (hmass : ∀ p, partitionFormMass B ρ (Ω p)=0) :
    IsPrimitiveFamily Ω (fun p => surfaceCovectorOperator B B₀ ρ D (Ω p)) ∧
      (∀ p x, x ∉ surfaceCovectorSupport B B₀ D →
        surfaceCovectorOperator B B₀ ρ D (Ω p) x=0) := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let Ωi := partitionTwoForm ρ Ω
  let Ki : I → Set M := fun i => K ∩ tsupport (ρ i)
  have hKi (i : I) : IsCompact (Ki i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hKiB (i : I) : Ki i ⊆ (B i).carrier := fun _ hx => hρ i hx.2
  have hΩi (i : I) : SmoothTwoFormFamily (Ωi i) := partitionTwoForm_smooth ρ hΩ i
  have hzΩi (i : I) : ∀ p x, x ∉ Ki i → Ωi i p x=0 := partitionTwoForm_zero ρ hz i
  have hsΩi (i : I) : ∀ p x u v, Ωi i p x u v = -Ωi i p x v u :=
    partitionTwoForm_skew ρ hskew i
  let m : I → P → ℝ := fun i p => chartMass (B i).center (Ωi i p)
  have hm (i : I) : ContDiff ℝ ∞ (m i) :=
    chartMass_smooth (hΩi i (B i).center) (hKi i) (fun x hx => (hKiB i hx).1) (hzΩi i)
  let Ξ : I → P → ManifoldTwoForm Plane M := fun i p => Ωi i p-m i p • (D.bump i).form
  have hlocal (i : I) : IsPrimitiveFamily (Ξ i) (fun p => boxCovectorOperator (B i) (Ξ i p)) ∧
      ∀ p x, x ∉ (B i).compactCarrier → boxCovectorOperator (B i) (Ξ i p) x=0 := by
    have hscaled : SmoothTwoFormFamily (fun p => m i p • (D.bump i).form) :=
      (SmoothTwoFormFamily.const (D.bump i).smooth).smul (hm i)
    have hdif : SmoothTwoFormFamily (Ξ i) := (hΩi i).sub hscaled
    have ha : ∀ p x u v, Ξ i p x u v = -Ξ i p x v u := by
      intro p x u v
      change Ωi i p x u v - m i p * (D.bump i).form x u v =
        -(Ωi i p x v u - m i p * (D.bump i).form x v u)
      rw [hsΩi i p x u v,(D.bump i).skew x u v]; ring
    have hzero : ∀ p x, x ∉ Ki i ∪ (D.bump i).supportSet → Ξ i p x=0 := by
      intro p x hx
      change Ωi i p x - m i p • (D.bump i).form x=0
      rw [hzΩi i p x (fun hk => hx (Or.inl hk)),
        (D.bump i).zero_off x (fun hk => hx (Or.inr hk))]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change (0 : ℝ) - m i p * 0 = 0
      rw [mul_zero,sub_self]
    have hmasslocal : ∀ p, chartMass (B i).center (Ξ i p)=0 := by
      intro p
      have h1 := (hΩi i).eval p |>.coefficient_integrable (B i).center (hKi i)
        (fun x hx => (hKiB i hx).1) (hzΩi i p)
      have h2 := hscaled.eval p |>.coefficient_integrable (B i).center (D.bump i).compact_supportSet
        (fun x hx => ((D.bump i).support_subset hx).1)
        (fun x hx => by
          change m i p • (D.bump i).form x=0
          rw [(D.bump i).zero_off x hx]
          apply ContinuousLinearMap.ext
          intro first
          apply ContinuousLinearMap.ext
          intro second
          exact mul_zero _)
      change chartMass (B i).center (Ωi i p-m i p • (D.bump i).form)=0
      rw [chartMass_sub h1 h2,chartMass_smul,(D.bump i).unit_mass,mul_one]
      exact sub_self _
    have hh := boxCovectorOperator_spec (B i) hdif ha ((hKi i).union (D.bump i).compact_supportSet)
      (union_subset (hKiB i) (D.bump i).support_subset) hzero hmasslocal
    exact ⟨⟨hh.1,hh.2.2⟩,hh.2.1⟩
  let α : I → P → ManifoldOneForm Plane M := fun i p =>
    boxCovectorOperator (B i) (Ξ i p) + m i p • D.primitive i
  have hα (i : I) : IsPrimitiveFamily (fun p => Ωi i p-m i p • D.common.form) (α i) := by
    have ht := ((D.primitive_spec i).const_slice (P := P) 0).smul (hm i)
    have hh := (hlocal i).1.add ht
    have he : (Ξ i + fun p => m i p • ((D.bump i).form-D.common.form)) =
        (fun p => Ωi i p - m i p • D.common.form) := by
      funext p x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change Ωi i p x u v - m i p * (D.bump i).form x u v +
        m i p * ((D.bump i).form x u v - D.common.form x u v) =
          Ωi i p x u v - m i p * D.common.form x u v
      ring
    exact he ▸ hh
  have hall := IsPrimitiveFamily.sum Finset.univ (fun i _ => hα i)
  have he : (∑ i, fun p => Ωi i p-m i p • D.common.form)=Ω := by
    funext p x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [Finset.sum_apply,sum_apply,Pi.sub_apply,Pi.smul_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul]
    have hm0 : (∑ i, m i p)=0 := hmass p
    rw [hm0,zero_mul,sub_zero]
    have hh := congrArg (fun F : P → ManifoldTwoForm Plane M => F p x u v)
      (partitionTwoForm_sum ρ hz)
    simpa only [Finset.sum_apply,sum_apply] using hh
  have hαsum : (∑ i, α i) = fun p => surfaceCovectorOperator B B₀ ρ D (Ω p) := by
    funext p x
    simp only [Finset.sum_apply,surfaceCovectorOperator,α,Ξ,m,Ωi,Pi.add_apply,Pi.smul_apply]
    rfl
  refine ⟨hαsum ▸ he ▸ hall,?_⟩
  intro p x hx
  change (∑ i, α i p) x=0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hxi : x ∉ (B i).compactCarrier ∪ D.supportSet i := fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩)
  change boxCovectorOperator (B i) (Ξ i p) x + m i p • D.primitive i x=0
  rw [(hlocal i).2 p x (fun hi => hxi (Or.inl hi)),D.zero_off i x (fun hi => hxi (Or.inr hi)),
    smul_zero,add_zero]

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K : Set M}

def partitionPiece (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω : ManifoldTwoForm Plane M) (i : I) : ManifoldTwoForm Plane M := fun x => ρ i x • Ω x

theorem partitionPiece_smooth [IsManifold 𝓘(ℝ,Plane) ∞ M] (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (i : I) : SmoothTwoForm (partitionPiece ρ Ω i) :=
  ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0

theorem partitionPiece_add (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (Ω Λ : ManifoldTwoForm Plane M) (i : I) :
    partitionPiece ρ (Ω+Λ) i = partitionPiece ρ Ω i + partitionPiece ρ Λ i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact mul_add (ρ i x) (Ω x u v) (Λ x u v)

theorem partitionPiece_smul (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) (i : I) :
    partitionPiece ρ (a • Ω) i = a • partitionPiece ρ Ω i := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change ρ i x * (a * Ω x u v) = a * (ρ i x * Ω x u v)
  ring

theorem partitionPiece_zero (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    {Ω : ManifoldTwoForm Plane M} (hz : ∀ x, x ∉ K → Ω x=0) (i : I) (x : M)
    (hx : x ∉ K ∩ tsupport (ρ i)) : partitionPiece ρ Ω i x=0 :=
  partitionTwoForm_zero (P := ℝ) ρ (fun _ => hz) i 0 x hx

def correctedPartitionPiece (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    (Ω : ManifoldTwoForm Plane M) (i : I) : ManifoldTwoForm Plane M :=
  partitionPiece ρ Ω i - chartMass (B i).center (partitionPiece ρ Ω i) • (D.bump i).form

theorem correctedPartitionPiece_smooth [IsManifold 𝓘(ℝ,Plane) ∞ M] (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (i : I) :
    SmoothTwoForm (correctedPartitionPiece B B₀ ρ D Ω i) :=
  ((SmoothTwoFormFamily.const (P := ℝ) (partitionPiece_smooth ρ hΩ i)).sub
    ((SmoothTwoFormFamily.const (P := ℝ) (D.bump i).smooth).smul contDiff_const)).eval 0

theorem correctedPartitionPiece_zero (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    {Ω : ManifoldTwoForm Plane M} (hz : ∀ x, x ∉ K → Ω x=0) (i : I) (x : M)
    (hx : x ∉ (K ∩ tsupport (ρ i)) ∪ (D.bump i).supportSet) :
    correctedPartitionPiece B B₀ ρ D Ω i x=0 := by
  unfold correctedPartitionPiece
  simp only [Pi.sub_apply,Pi.smul_apply]
  rw [partitionPiece_zero ρ hz i x (fun hk => hx (Or.inl hk)),
    (D.bump i).zero_off x (fun hb => hx (Or.inr hb))]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change (0 : ℝ)-_ * 0=0
  ring

theorem correctedPartitionPiece_smul (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) (i : I) :
    correctedPartitionPiece B B₀ ρ D (a • Ω) i = a • correctedPartitionPiece B B₀ ρ D Ω i := by
  unfold correctedPartitionPiece
  rw [partitionPiece_smul,chartMass_smul]
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change a * partitionPiece ρ Ω i x u v - (a * chartMass (B i).center (partitionPiece ρ Ω i)) *
    (D.bump i).form x u v = a * (partitionPiece ρ Ω i x u v -
      chartMass (B i).center (partitionPiece ρ Ω i) * (D.bump i).form x u v)
  ring

theorem surfaceCovectorOperator_smul [Fintype I] (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (D : SurfaceMassTransferData B B₀)
    (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    surfaceCovectorOperator B B₀ ρ D (a • Ω) = a • surfaceCovectorOperator B B₀ ρ D Ω := by
  classical
  change (∑ i, (boxCovectorOperator (B i) (correctedPartitionPiece B B₀ ρ D (a • Ω) i) +
    chartMass (B i).center (partitionPiece ρ (a • Ω) i) • D.primitive i)) = _
  simp_rw [correctedPartitionPiece_smul,boxCovectorOperator_smul,partitionPiece_smul,chartMass_smul,
    mul_smul,← smul_add]
  exact (Finset.smul_sum ..).symm

theorem correctedPartitionPiece_add [IsManifold 𝓘(ℝ,Plane) ∞ M] (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ K → Λ x=0) (i : I) :
    correctedPartitionPiece B B₀ ρ D (Ω+Λ) i =
      correctedPartitionPiece B B₀ ρ D Ω i + correctedPartitionPiece B B₀ ρ D Λ i := by
  have h1 := (partitionPiece_smooth ρ hΩ i).coefficient_integrable (B i).center
    (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΩ i)
  have h2 := (partitionPiece_smooth ρ hΛ i).coefficient_integrable (B i).center
    (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΛ i)
  unfold correctedPartitionPiece
  rw [partitionPiece_add,chartMass_add h1 h2]
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change partitionPiece ρ Ω i x u v + partitionPiece ρ Λ i x u v -
    (chartMass (B i).center (partitionPiece ρ Ω i) + chartMass (B i).center (partitionPiece ρ Λ i)) *
      (D.bump i).form x u v =
    (partitionPiece ρ Ω i x u v-chartMass (B i).center (partitionPiece ρ Ω i)*(D.bump i).form x u v) +
    (partitionPiece ρ Λ i x u v-chartMass (B i).center (partitionPiece ρ Λ i)*(D.bump i).form x u v)
  ring

theorem surfaceCovectorOperator_add [Fintype I] [IsManifold 𝓘(ℝ,Plane) ∞ M] (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ K → Λ x=0) :
    surfaceCovectorOperator B B₀ ρ D (Ω+Λ) =
      surfaceCovectorOperator B B₀ ρ D Ω + surfaceCovectorOperator B B₀ ρ D Λ := by
  classical
  change (∑ i, (boxCovectorOperator (B i) (correctedPartitionPiece B B₀ ρ D (Ω+Λ) i) +
    chartMass (B i).center (partitionPiece ρ (Ω+Λ) i) • D.primitive i)) = _
  have hc (i : I) : IsCompact ((K ∩ tsupport (ρ i)) ∪ (D.bump i).supportSet) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).union (D.bump i).compact_supportSet
  have hb (i : I) : ((K ∩ tsupport (ρ i)) ∪ (D.bump i).supportSet) ⊆ (B i).carrier :=
    union_subset (fun _ hx => hρ i hx.2) (D.bump i).support_subset
  have hadd (i : I) : boxCovectorOperator (B i) (correctedPartitionPiece B B₀ ρ D (Ω+Λ) i) =
      boxCovectorOperator (B i) (correctedPartitionPiece B B₀ ρ D Ω i) +
      boxCovectorOperator (B i) (correctedPartitionPiece B B₀ ρ D Λ i) := by
    rw [correctedPartitionPiece_add hK B B₀ ρ hρ D hΩ hΛ hzΩ hzΛ]
    exact boxCovectorOperator_add (B i) (correctedPartitionPiece_smooth B B₀ ρ D hΩ i)
      (correctedPartitionPiece_smooth B B₀ ρ D hΛ i) (hc i) (hc i) (hb i) (hb i)
      (correctedPartitionPiece_zero B B₀ ρ D hzΩ i) (correctedPartitionPiece_zero B B₀ ρ D hzΛ i)
  have hmadd (i : I) : chartMass (B i).center (partitionPiece ρ (Ω+Λ) i) =
      chartMass (B i).center (partitionPiece ρ Ω i)+chartMass (B i).center (partitionPiece ρ Λ i) := by
    rw [partitionPiece_add]
    exact chartMass_add
      ((partitionPiece_smooth ρ hΩ i).coefficient_integrable (B i).center
        (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΩ i))
      ((partitionPiece_smooth ρ hΛ i).coefficient_integrable (B i).center
        (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΛ i))
  simp_rw [hadd,hmadd,add_smul]
  simp only [surfaceCovectorOperator,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact add_add_add_comm _ _ _ _

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

def smoothSupportedTwoForms (K : Set M) : Submodule ℝ (ManifoldTwoForm E M) where
  carrier := {Ω | SmoothTwoForm Ω ∧ (∀ x u v, Ω x u v = -Ω x v u) ∧ ∀ x, x ∉ K → Ω x=0}
  zero_mem' := by
    refine ⟨?_,?_,?_⟩
    · intro c
      rw [show chartTwoForm (0 : ManifoldTwoForm E M) c = fun _ => 0 from
        funext (fun y => chartTwoForm_zero c y)]
      exact contDiffOn_const
    · intro x u v
      simp only [Pi.zero_apply,zero_apply,neg_zero]
    · intro x _
      rfl
  add_mem' := by
    intro Ω Λ hΩ hΛ
    refine ⟨((SmoothTwoFormFamily.const (P := ℝ) hΩ.1).add
      (SmoothTwoFormFamily.const (P := ℝ) hΛ.1)).eval 0,?_,?_⟩
    · intro x u v
      change Ω x u v+Λ x u v = -(Ω x v u+Λ x v u)
      rw [hΩ.2.1 x u v,hΛ.2.1 x u v,neg_add]
    · intro x hx
      change Ω x+Λ x=0
      rw [hΩ.2.2 x hx,hΛ.2.2 x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact zero_add (0 : ℝ)
  smul_mem' := by
    intro a Ω hΩ
    refine ⟨((SmoothTwoFormFamily.const (P := ℝ) hΩ.1).smul
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => a))).eval 0,?_,?_⟩
    · intro x u v
      change a*Ω x u v = -(a*Ω x v u)
      rw [hΩ.2.1 x u v,mul_neg]
    · intro x hx
      change a • Ω x=0
      rw [hΩ.2.2 x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero a

theorem smoothSupportedTwoForms.smooth {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K) :
    SmoothTwoForm (Ω : ManifoldTwoForm E M) := Ω.property.1

theorem smoothSupportedTwoForms.skew {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K)
    (x : M) (u v : E) : (Ω : ManifoldTwoForm E M) x u v = -(Ω : ManifoldTwoForm E M) x v u :=
  Ω.property.2.1 x u v

theorem smoothSupportedTwoForms.zero_off {K : Set M} (Ω : smoothSupportedTwoForms (E := E) K)
    (x : M) (hx : x ∉ K) : (Ω : ManifoldTwoForm E M) x=0 := Ω.property.2.2 x hx

end

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

def surfacePrimitiveLinearMap (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀) :
    smoothSupportedTwoForms (E := Plane) K →ₗ[ℝ] ManifoldOneForm Plane M where
  toFun Ω := surfaceCovectorOperator B B₀ ρ D Ω
  map_add' Ω Λ := surfaceCovectorOperator_add hK B B₀ ρ hρ D (smoothSupportedTwoForms.smooth Ω) (smoothSupportedTwoForms.smooth Λ) (smoothSupportedTwoForms.zero_off Ω) (smoothSupportedTwoForms.zero_off Λ)
  map_smul' a Ω := surfaceCovectorOperator_smul B B₀ ρ D a Ω

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem partitionFormMass_smul (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (a : ℝ) (Ω : ManifoldTwoForm Plane M) :
    partitionFormMass B ρ (a • Ω) = a * partitionFormMass B ρ Ω := by
  change (∑ i, chartMass (B i).center (partitionPiece ρ (a • Ω) i)) = _
  simp_rw [partitionPiece_smul,chartMass_smul]
  exact (Finset.mul_sum ..).symm

theorem partitionFormMass_add (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x, x ∉ K → Ω x=0) (hzΛ : ∀ x, x ∉ K → Λ x=0) :
    partitionFormMass B ρ (Ω+Λ) = partitionFormMass B ρ Ω + partitionFormMass B ρ Λ := by
  change (∑ i, chartMass (B i).center (partitionPiece ρ (Ω+Λ) i)) = _
  unfold partitionFormMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [partitionPiece_add]
  exact chartMass_add
    ((partitionPiece_smooth ρ hΩ i).coefficient_integrable (B i).center
      (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΩ i))
    ((partitionPiece_smooth ρ hΛ i).coefficient_integrable (B i).center
      (hK.inter_right (isClosed_tsupport (ρ i))) (fun _ hx => (hρ i hx.2).1) (partitionPiece_zero ρ hzΛ i))

def surfaceIntegralLinearMap (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) :
    smoothSupportedTwoForms (E := Plane) K →ₗ[ℝ] ℝ where
  toFun Ω := partitionFormMass B ρ Ω
  map_add' Ω Λ := partitionFormMass_add hK B ρ hρ (smoothSupportedTwoForms.smooth Ω) (smoothSupportedTwoForms.smooth Λ) (smoothSupportedTwoForms.zero_off Ω) (smoothSupportedTwoForms.zero_off Λ)
  map_smul' a Ω := partitionFormMass_smul B ρ a Ω

theorem surfacePrimitiveLinearMap_spec [T2Space M]
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M) (B₀ : SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (D : SurfaceMassTransferData B B₀)
    (Ω : P → smoothSupportedTwoForms (E := Plane) K)
    (hΩ : SmoothTwoFormFamily (fun p => (Ω p : ManifoldTwoForm Plane M)))
    (hmass : ∀ p, surfaceIntegralLinearMap hK B ρ hρ (Ω p)=0) :
    IsPrimitiveFamily (fun p => (Ω p : ManifoldTwoForm Plane M))
      (fun p => surfacePrimitiveLinearMap hK B B₀ ρ hρ D (Ω p)) ∧
      (∀ p x, x ∉ surfaceCovectorSupport B B₀ D →
        surfacePrimitiveLinearMap hK B B₀ ρ hρ D (Ω p) x=0) :=
  surfaceCovectorOperator_spec hK B B₀ ρ hρ D hΩ (fun p => smoothSupportedTwoForms.skew (Ω p))
    (fun p => smoothSupportedTwoForms.zero_off (Ω p)) hmass

end

section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 theorem partitionFormMass_eq_chartMass {I : Type*} [Fintype I] {K L : Set M}
    (hor : PositivePlaneTransitions M) (hL : IsCompact L) (hLK : L⊆K)
    (c : M) (hLc : L⊆(extChartAt 𝓘(ℝ,Plane) c).source)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω)
    (ha : ∀ x u v,Ω x u v= -Ω x v u) (hz : ∀ x,x∉L→Ω x=0) :
    partitionFormMass B ρ Ω=chartMass c Ω := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let D : I → ManifoldTwoForm Plane M := fun i x => ρ i x • Ω x
  let C : I → Set M := fun i => L∩tsupport (ρ i)
  have hC (i : I) : IsCompact (C i) := hL.inter_right (isClosed_tsupport (ρ i))
  have hCB (i : I) : C i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hCc (i : I) : C i⊆(extChartAt 𝓘(ℝ,Plane) c).source := fun _ hx => hLc hx.1
  have hDs (i : I) : SmoothTwoForm (D i) :=
    ((SmoothTwoFormFamily.const (P := ℝ) hΩ).spatial_smul (ρ i).contMDiff).eval 0
  have hDa (i : I) (x : M) (u v : Plane) : D i x u v= -D i x v u := by
    change ρ i x * Ω x u v= -(ρ i x * Ω x v u)
    rw [ha x u v,mul_neg]
  have hDz (i : I) (x : M) (hx : x∉C i) : D i x=0 := by
    by_cases hk : x∈L
    · have hi : x∉tsupport (ρ i) := fun hi => hx ⟨hk,hi⟩
      simp only [D,image_eq_zero_of_notMem_tsupport hi,zero_smul]
    · simp only [D,hz x hk,smul_zero]
  have hsum : (∑ i,D i)=Ω := by
    funext x
    simp only [Finset.sum_apply,D,← Finset.sum_smul]
    by_cases hx : x∈L
    · have hs : (∑ i,ρ i x)=1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (hLK hx)
      rw [hs,one_smul]
    · rw [hz x hx]
      apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact mul_zero _
  have hc (i : I) : chartMass (B i).center (D i)=chartMass c (D i) := by
    apply chartMass_change (hDa i) (hC i) (hCB i) (hCc i) (hDz i)
    rintro y ⟨x,hx,rfl⟩
    apply hor (B i).center c _ ((extChartAt 𝓘(ℝ,Plane) (B i).center).map_source (hCB i hx))
    simpa only [(extChartAt 𝓘(ℝ,Plane) (B i).center).left_inv (hCB i hx)] using hCc i hx
  change (∑ i,chartMass (B i).center (D i))=_
  simp_rw [hc]
  rw [← chartMass_sum Finset.univ c D
    (fun i _ => (hDs i).coefficient_integrable c (hC i) (hCc i) (hDz i)),hsum]

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

 theorem partitionFormMass_compact_stokes {I : Type*} [Fintype I] {K : Set M}
    (hor : PositivePlaneTransitions M) (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→α x=0) : partitionFormMass B ρ (manifoldExteriorOneForm α)=0 := by
  classical
  let β : I → ManifoldOneForm Plane M := fun i x => ρ i x • α x
  let L : I → Set M := fun i => K∩tsupport (ρ i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hLB (i : I) : L i⊆(extChartAt 𝓘(ℝ,Plane) (B i).center).source :=
    fun _ hx => (hρ i hx.2).1
  have hβs (i : I) : SmoothOneFormFamily (fun _ : ℝ => β i) := hα.spatial_smul (ρ i).contMDiff
  have hβz (i : I) (x : M) (hx : x∉L i) : β i x=0 := by
    change ρ i x • α x=0
    by_cases hk : x∈K
    · rw [image_eq_zero_of_notMem_tsupport (fun hi => hx ⟨hk,hi⟩),zero_smul]
    · rw [hz x hk,smul_zero]
  have hdz (i : I) (x : M) (hx : x∉L i) : manifoldExteriorOneForm (β i) x=0 :=
    manifoldExteriorOneForm_zero_off (hL i).isClosed (hβz i) hx
  have hsum : (∑ i,β i)=α := by
    funext x
    simp only [Finset.sum_apply,β,← Finset.sum_smul]
    by_cases hx : x∈K
    · have hs : (∑ i,ρ i x)=1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
      rw [hs,one_smul]
    · rw [hz x hx,smul_zero]
  let D : I → smoothSupportedTwoForms (E := Plane) K := fun i =>
    ⟨manifoldExteriorOneForm (β i),
      (manifoldExteriorOneForm_family_smooth (hβs i)).eval 0,
      manifoldExteriorOneForm_skew (β i),fun x hx => hdz i x (fun hi => hx hi.1)⟩
  have hdSum : ((∑ i,D i : smoothSupportedTwoForms (E := Plane) K) : ManifoldTwoForm Plane M)=
      manifoldExteriorOneForm α := by
    funext x
    simp only [Submodule.coe_sum,Finset.sum_apply]
    change (∑ i,manifoldExteriorOneForm (β i) x)=manifoldExteriorOneForm α x
    rw [← manifoldExteriorOneForm_sum Finset.univ (fun i _ => hβs i) (0 : ℝ),hsum]
  have hmass (i : I) : surfaceIntegralLinearMap hK B ρ hρ (D i)=0 := by
    change partitionFormMass B ρ (manifoldExteriorOneForm (β i))=0
    rw [partitionFormMass_eq_chartMass hor (hL i) inter_subset_left
      (B i).center (hLB i) B ρ hρ ((manifoldExteriorOneForm_family_smooth (hβs i)).eval 0)
      (manifoldExteriorOneForm_skew (β i)) (hdz i)]
    exact chartMass_exterior_eq_zero (hL i) (hLB i) (hβs i) (hβz i)
  rw [← hdSum]
  change surfaceIntegralLinearMap hK B ρ hρ (∑ i,D i)=0
  rw [map_sum]
  simp only [hmass,Finset.sum_const_zero]

 theorem compactSurfaceFormIntegral_compact_stokes [SigmaCompactSpace M]
    [MeasurableSpace M] [BorelSpace M] {K : Set M}
    (hor : PositivePlaneTransitions M) (hK : IsCompact K)
    {α : ManifoldOneForm Plane M} (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (hz : ∀ x,x∉K→α x=0) : compactSurfaceFormIntegral hK (manifoldExteriorOneForm α)=0 := by
  have hdz (x : M) (hx : x∉K) : manifoldExteriorOneForm α x=0 :=
    manifoldExteriorOneForm_zero_off hK.isClosed hz hx
  unfold compactSurfaceFormIntegral
  rw [restrictedPartitionFormMass_eq_indicator _ _ hK.measurableSet]
  have he : K.indicator (manifoldExteriorOneForm α)=manifoldExteriorOneForm α := by
    funext x
    by_cases hx : x∈K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hdz x hx]
  rw [he]
  exact partitionFormMass_compact_stokes hor hK _ _ (compactSurfacePartition_subordinate hK) hα hz

end PackingSufficiencySupport.Hamiltonian
end

end OAI
