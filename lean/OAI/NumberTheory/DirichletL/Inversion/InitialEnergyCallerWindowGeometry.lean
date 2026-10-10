import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerWindowGeometry
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerGeometry
open InverseInitialProfile InverseInitialKernelBridge ConcreteTraceCRT
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖eisEmbedding x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact ⟨(∅,∅),by simp,rfl⟩
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖eisEmbedding x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h0.2,
    (le_div_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.1,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h1.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h2.2,
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ _)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

theorem retained_child_boxes
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hhi:∀i,0≤hi i)
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H)(u:Eisˣ) :
    ((initialChild (toTuple p (sectorSource u x))).2.1.absNorm:ℝ)≤
      (hi 1*hi 2)*Z^(θ+v) ∧
    ‖eisEmbedding (initialChild (toTuple p (sectorSource u x))).2.2‖^2≤
      (hi 1*hi 3)*Z^(θ+H) := by
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [initial_child_label_norm p,initial_child_row_norm p hp hpr]
  constructor
  · apply (mul_le_mul h1 h2 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring
  · apply (mul_le_mul h1 h3 (by positivity) (mul_nonneg (hhi 1) (Real.rpow_nonneg hZ.le _))).trans_eq
    rw [Real.rpow_add hZ]
    ring

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_source_quotients
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))(hlo:0<lo 1)(hhi:0≤hi 0)
    (Z D B v θ H:ℝ)(hZ:0<Z) :
    ∀t∈InverseInitialQuotientGeometry.quotientSet p (windowSource p S ψ Z D B v θ H),
      (t.absNorm:ℝ)≤(hi 0/lo 1)*Z^(B-θ) := by
  intro t ht
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨h0,h1lo,h1,h2,h3⟩ := retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  rw [InverseInitialQuotientGeometry.quotient_norm_eq p hp x (hdiv x (Finset.mem_filter.mp hx).1)]
  apply (div_le_div₀ (by positivity) h0 (mul_pos hlo (Real.rpow_pos_of_pos hZ _)) h1lo).trans_eq
  rw [Real.rpow_sub hZ]
  ring

end SevenEighths.InverseInitialEnergyCallerWindowGeometry

end

end OAI
