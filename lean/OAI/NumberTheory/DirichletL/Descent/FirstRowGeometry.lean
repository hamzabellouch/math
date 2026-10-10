import OAI.NumberTheory.DirichletL.Descent.PhysicalExponents
import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma first_whole_frequency_numeric (K P dn an cn a1 a2 sn tn hn L : ℝ)
    (hK : 0<K) (hP : 0<P) (hdn : 0<dn) (han : 0<an)
    (hcn : 0<cn) (ha1 : 0<a1) (ha2 : 0<a2)
    (hsn : 0<sn) (htn : 0<tn) (_hhn : 0≤hn) (hL : 0<L)
    (hS : a1*cn*sn≤L) (hT : a2*cn*tn≤L)
    (hratio : (K/(dn*(sn*tn*an)))*hn≤P) :
    hn≤L^2*an*dn/((K/P)*a1*a2*cn^2) := by
  have hprod : sn*tn*(a1*a2*cn^2)≤L^2 := by
    have hh := mul_le_mul hS hT (by positivity : 0≤a2*cn*tn) hL.le
    nlinarith [hh]
  have hraw : K*hn≤P*(dn*(sn*tn*an)) := by
    rw [div_mul_eq_mul_div] at hratio
    exact (div_le_iff₀ (by positivity)).mp hratio
  have hfull : K*hn*(a1*a2*cn^2)≤P*dn*an*L^2 := by
    have hh := mul_le_mul_of_nonneg_right hraw (by positivity : 0≤a1*a2*cn^2)
    have hh' := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤P*dn*an)
    nlinarith [hh,hh']
  apply (le_div_iff₀ (by positivity)).mpr
  convert div_le_div_of_nonneg_right hfull hP.le using 1 <;> field_simp

theorem first_ratio_actual_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (K P L B F : ℝ) (hK : 0<K) (hP : 0<P) (hL : 0<L) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B)
    (hf : (Ideal.absNorm f : ℝ)≤F)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤L)
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤L)
    (hratio : (K/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤P) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
    P*L^2*B^4*F^2*primeProductNorm p divisor /
      (K*(primeProductNorm p common)^2*‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) := by
  let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let e := dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let j := jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let a1 := aLabel p S ε₁
  let a2 := aLabel p S ε₂
  have hactive : active ⊆ S := Finset.filter_subset _ _
  have hnorm : primeProductNorm p ((N∪Q)∪active)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p active := by
    rw [primeProductNorm_union p (N∪Q) active (Finset.disjoint_union_left.mpr
      ⟨hNS.mono_right hactive,hQS.mono_right hactive⟩),
      primeProductNorm_union p _ _ hNQ]
  change (K/(primeProductNorm p divisor*primeProductNorm p ((N∪Q)∪active)))*‖eisEmbedding h‖^2≤P at hratio
  rw [hnorm] at hratio
  have hpos (v : ι→ℕ) : 0<‖eisEmbedding (primeProduct p S v)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hfreq := first_whole_frequency_numeric K P (primeProductNorm p divisor)
    (primeProductNorm p active) (primeProductNorm p common) (‖eisEmbedding a1‖^2)
    (‖eisEmbedding a2‖^2) (primeProductNorm p N) (primeProductNorm p Q)
    (‖eisEmbedding h‖^2) L hK hP (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (hpos _) (hpos _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (sq_nonneg _) hL hcol₁ hcol₂ hratio
  have hcon := first_conductor_norm_bound p hp S v₁ v₂ ε₁ ε₂ hv B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2)
    (‖eisEmbedding j‖^2) (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2)
    (primeProductNorm p common) (primeProductNorm p divisor) (‖eisEmbedding h‖^2)
    (Ideal.absNorm f) L (K/P) B F (primeProductNorm_pos p hp _).le (sq_nonneg _)
    (hpos _) (hpos _) (hpos _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _).le
    (sq_nonneg _) (Nat.cast_nonneg _) hL (div_pos hK hP) hB hF hcon hfreq hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator f)‖^2=(Ideal.absNorm f : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e (f,h))‖^2 =
      ‖eisEmbedding h‖^2*(Ideal.absNorm f : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [hgen]
  rw [hrow]
  apply hnum.trans_eq
  field_simp
  ring

end
end SevenEighths.InverseMoment

end OAI
