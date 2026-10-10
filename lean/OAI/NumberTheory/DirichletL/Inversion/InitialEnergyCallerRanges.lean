import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSourceMask

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerRanges
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerGeometry InverseInitialEnergyCallerSourceMask
open InverseInitialProfile ConcreteTraceCRT CanonicalQuadraticSieve
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
  (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp hcop hg

omit [DecidableEq ι] in
theorem sourceIdeal_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset ι) : Admissible (sourceIdeal p S) := by
  refine ⟨sourceIdeal_ne_zero p hp S,sourceIdeal_squarefree p hcop S,?_⟩
  intro P hP
  obtain ⟨hprime,hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff
    (sourceIdeal_ne_zero p hp S)).mp hP
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod] at hdiv
  obtain ⟨i,hi,hPi⟩ := (hprime.dvd_finsetProd_iff (fun i=>Ideal.span {p i})).mp hdiv
  have he := (prime_dvd_prime_iff_eq hprime (sourcePrime p i).property).mp hPi
  rw [he]
  exact ⟨hg i,hc i⟩

theorem retained_label_admissible (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    {x:Source (ι:=ι) 0}(hx:x∈coprimeSource p S)(u:Eisˣ) :
    Admissible (initialChild (toTuple p (sectorSource u x))).2.1 := by
  have hs := (supported_mul_iff (sourceIdeal p x.divisor) (sourceIdeal p x.overlap)).mpr
    ⟨admissible_supported (sourceIdeal_admissible p hp hcop hg hc _),
      admissible_supported (sourceIdeal_admissible p hp hcop hg hc _)⟩
  exact ⟨hs.1,retained_child_squarefree p hcop S hdiv hx u,hs.2⟩

theorem childLabels_subset_range
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (Z θ v η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η)) :
    childLabels p S⊆idealRange (Z^(θ+v+2*η)) := by
  intro f hf
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
  apply mem_idealRange.mpr
  refine ⟨retained_label_admissible p hp hcop hg hc S hdiv hx 1,?_⟩
  change ((sourceIdeal p x.divisor*sourceIdeal p x.overlap).absNorm:ℝ)≤_
  rw [map_mul,Nat.cast_mul]
  apply (mul_le_mul (hd x hx) (hv x hx) (by positivity) (by positivity)).trans_eq
  rw [←Real.rpow_add hZ]
  congr 1
  ring

theorem canonical_child_domains
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)
    (hf:∀x∈S,x.frequency≠0)(Z θ v H η:ℝ)(hZ:0<Z)
    (hd:∀x∈coprimeSource p S,((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η))
    (hv:∀x∈coprimeSource p S,((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η))
    (hh:∀x∈coprimeSource p S,‖eisEmbedding x.frequency‖^2≤Z^(H+η)) :
    ∀x∈coprimeSource p S,∀u:Eisˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  intro x hx u
  refine ⟨childLabels_subset_range p hp hcop hg hc hpr S hdiv Z θ v η hZ hd hv
    (child_label_mem p S hx u),?_⟩
  rw [initial_child_row_ball p hp hpr]
  refine ⟨mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr
    (eisEmbedding_ne_zero (hf x (Finset.mem_filter.mp hx).1)))),?_⟩
  · exact_mod_cast Nat.pos_of_ne_zero (fun h=>sourceIdeal_ne_zero p hp x.divisor
      (Ideal.absNorm_eq_zero_iff.mp h))
  · have he := (initial_child_enclosures p hp hpr x u Z θ v H η hZ
      (hd x hx) (hv x hx) (hh x hx)).2
    rwa [initial_child_row_norm p hp hpr] at he

end SevenEighths.InverseInitialEnergyCallerRanges

end

end OAI
