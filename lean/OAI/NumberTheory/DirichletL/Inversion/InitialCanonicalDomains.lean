import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindowGeometry

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalDomains
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerWindows InverseInitialEnergyCallerWindowGeometry
open InverseInitialEnergyCallerSourceMask InverseInitialEnergyCallerRanges
open InverseInitialEnergyCallerSource CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem window_power_bounds
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H):
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤Z^(θ+η) ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤Z^(v+η) ∧
    ‖eisEmbedding x.frequency‖^2≤Z^(H+η) := by
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hZ hx
  have hpow (i:Fin 4)(r:ℝ):hi i*Z^r≤Z^(r+η):=by
    rw [Real.rpow_add hZ]
    exact (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hZ.le _)).trans_eq (mul_comm _ _)
  exact ⟨hd.trans (hpow 1 θ),hv.trans (hpow 2 v),hh.trans (hpow 3 H)⟩

include hp hcop hg in
theorem actual_window_domains
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:0<Z)(hhi:∀i,hi i≤Z^η):
    ∀x∈coprimeSource p (windowSource p S ψ Z D B v θ H),∀u:Oˣ,
      (initialChild (toTuple p (sectorSource u x))).2.1∈idealRange (Z^(θ+v+2*η)) ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈
        nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)) := by
  apply canonical_child_domains p hp hcop hg hc hpr (windowSource p S ψ Z D B v θ H)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1) Z θ v H η hZ
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.1
  · intro x hx
    exact (window_power_bounds p S ψ lo hi hψ Z D B v θ H η hZ hhi (Finset.mem_filter.mp hx).1).2.2

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem retained_quotient_subset
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ):
    quotientSet p (coprimeSource p (windowSource p S ψ Z D B v θ H))⊆
      quotientSet p (windowSource p S ψ Z D B v θ H) :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end SevenEighths.InverseInitialCanonicalDomains

end

end OAI
