import OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
open InverseInitialArithmetic InverseInitialQuotientGeometry InverseInitialProfile
open InverseInitialEnergyCallerState InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerWindowGeometry InverseInitialEnergyCallerGeometry
open InverseInitialEnergyCallerRanges CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem live_widths_nonnegative
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H η:ℝ)(hZ:1<Z)(hhi:∀i,hi i≤Z^η)
    {x:Source (ι:=ι) 0}(hx:x∈windowSource p S ψ Z D B v θ H)
    (hf:x.frequency≠0):
    0≤θ+v+2*η ∧ 0≤θ+H+2*η := by
  have hz:=zero_lt_one.trans hZ
  obtain ⟨_,_,hd,hv,hh⟩:=retained_source_windows p S ψ lo hi hψ Z D B v θ H hz hx
  have bound (a c:ℝ)(i:Fin 4)(ha:a≤hi i*Z^c):a≤Z^(c+η):=by
    apply (ha.trans (mul_le_mul_of_nonneg_right (hhi i) (Real.rpow_nonneg hz.le c))).trans_eq
    rw [←Real.rpow_add hz]
    congr 1
    ring
  obtain ⟨hlabel,hrow⟩:=initial_child_enclosures p hp hpr x 1 Z θ v H η hz
    (bound _ _ 1 hd) (bound _ _ 2 hv) (bound _ _ 3 hh)
  have hI:(1:ℝ)≤Ideal.absNorm (initialChild (toTuple p (sectorSource 1 x))).2.1:=by
    have hne:(initialChild (toTuple p (sectorSource 1 x))).2.1≠0:=
      mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne)
  have hdiv:(1:ℝ)≤(sourceIdeal p x.divisor).absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _))
  have hfreq:(1:ℝ)≤‖eisEmbedding x.frequency‖^2:=by
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hf))
  have hr:(1:ℝ)≤‖eisEmbedding (initialChild (toTuple p (sectorSource 1 x))).2.2‖^2:=by
    rw [initial_child_row_norm p hp hpr]
    exact one_le_mul_of_one_le_of_one_le hdiv hfreq
  constructor
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hI.trans hlabel)
  · exact (Real.rpow_le_rpow_left_iff hZ).mp
      (by simpa only [Real.rpow_zero] using hr.trans hrow)

include hp in
omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem retained_full_puncture
    (hpr:∀i,λ₀^2∣p i-1)(S:Finset (Source (ι:=ι) 0))
    (ψ:Fin 4→ℝ→ℂ)(D v H aC bC ad bd Z B θ η G:ℝ)(hZ:1<Z)
    (hC:Function.support (ψ 0)⊆Set.Icc aC bC)
    (hd:Function.support (ψ 1)⊆Set.Icc ad bd)
    (hCup:bC≤Z^η)(hdlo:Z^(-η)≤ad)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (j:O)(hj:j≠0)(hnj:(Ideal.absNorm (Ideal.span {j}):ℝ)≤Z^(G+η))
    {t:Ideal O}(ht:t∈quotientSet p (windowSource p S ψ Z D B v θ H)):
    j*primaryGenerator t≠0 ∧ 0≤fullPunctureWidth Z t j ∧
    ‖eisEmbedding (j*primaryGenerator t)‖^2=Z^(fullPunctureWidth Z t j) ∧
    fullPunctureWidth Z t j≤B-θ+G+3*η := by
  have hspan:=span_source_puncture p hp (windowSource p S ψ Z D B v θ H) hpr j ht
  have ht0:=quotientSet_nonzero p hp (windowSource p S ψ Z D B v θ H) t ht
  have hm:j*primaryGenerator t≠0:=by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [hspan]
    exact mul_ne_zero ht0 (Ideal.span_singleton_eq_bot.not.mpr hj)
  have hret:=window_quotient_subset_retained p S ψ Z D B v θ H ht
  have hnt:=retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
    aC bC ad bd Z B θ η (zero_lt_one.trans hZ) hC hd hCup hdlo hdiv t hret
  obtain ⟨hn,he⟩:=full_puncture_width_exact Z hZ t j hm
  exact ⟨hm,hn,he,full_product_width_bound Z (B-θ) G η hZ t j hm hspan hnt hnj⟩

end SevenEighths.InverseInitialCanonicalState

end

end OAI
