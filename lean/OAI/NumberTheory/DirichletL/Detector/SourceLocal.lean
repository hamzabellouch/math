import OAI.NumberTheory.DirichletL.Detector.SpectralWeights
import OAI.NumberTheory.DirichletL.Detector.ZeroIndex

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def sourceScalar (t k j : ℕ) : ℂ :=
  if t=0 then
    if k=0 then 1 else (actualSextic (Ideal.span {p}) hg ^ k) (Ideal.Quotient.mk _ (p^j))
  else positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k j

def sourcePrincipalTerm (eta a x w z : ℂ) (e l k m : ℕ) : ℂ :=
  sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (6*m)) e l k m

lemma sourcePrincipalTerm_pos (eta a x w z : ℂ) (e l k m : ℕ) (ht : e+3*l≠0) :
    sourcePrincipalTerm p hp hg eta a x w z e l k m =
      principalMarkedTerm p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [sourceScalar, ht, ite_false, principalMarkedTerm, coordV, Complex.ofReal_natCast]

lemma sourcePrincipalTerm_zero (eta a x w z : ℂ) (k m : ℕ) :
    sourcePrincipalTerm p hp hg eta a x w z 0 0 k m =
      zeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [weightedScalar, localCubePhase, sourceScalar, zeroIndexTerm, coordV,
    mul_zero, add_zero, pow_zero,  one_mul, zero_mul, Nat.choose_zero_succ,
    ite_true, Complex.ofReal_natCast]

def sourcePrincipalSeries (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z e.val l k m

include hc in
lemma sourcePrincipalSeries_eq (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) := by
  dsimp only
  simp only [Complex.ofReal_natCast]
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1 := by
    have he := evenRatio_eq_coordR _ hQ a x z
    simp only [Complex.ofReal_natCast] at he
    change ‖evenRatio _ a _ _‖<1
    rw [he]
    exact hR
  have hW' : ‖W‖<1 := by simpa only [W, coordW, one_mul, Complex.ofReal_natCast] using hW
  have he : Summable (fun l => principalInner p hp hg eta a X W V 0 l) :=
    (principalInner_even_hasSum p hp hg hc eta a X W V hV hr).summable
  have h0 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 0 l k m) =
      (fun l => principalInner p hp hg eta a X W V 0 l +
        if l=0 then zeroIndexSeries p (actualSextic (Ideal.span {p}) hg) W V else 0) := by
    funext l
    by_cases hl : l=0
    · subst l
      simp only [sourcePrincipalTerm_zero, principalInner_zero p hp hg,  ite_true,
        zero_add, zeroIndexSeries, W, V]
    · rw [ite_eq_right hl, add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourcePrincipalTerm_pos p hp hg eta a x w z 0 l k m (by omega)
  have h1 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 1 l k m) =
      (fun l => principalInner p hp hg eta a X W V 1 l) := by
    funext l
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourcePrincipalTerm_pos p hp hg eta a x w z 1 l k m (by omega)
  unfold sourcePrincipalSeries principalFullSeries principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0, h1, he.tsum_add (hasSum_ite_eq 0 _).summable, tsum_ite_eq]
  rw [zeroIndexSeries_eq p hp _ W V hW' hV]
  change _ = 1/(1-V)+W/(1-W)+((∑' l, principalInner p hp hg eta a X W V 0 l)+
    ∑' l, principalInner p hp hg eta a X W V 1 l)
  ring

include hc in

theorem sourcePrincipalSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [sourcePrincipalSeries_eq p hp hg hc eta a x w z hV hR hW]
  exact principalFullSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end SevenEighths.ProbeEuler
end

end OAI
