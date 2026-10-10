import OAI.NumberTheory.DirichletL.Moments.RetainedReflection
import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentRetainedReflection CenteredMomentTwistedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def finiteAnnularColumn (η : Character) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

lemma finiteAnnularColumn_eq (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dite_eq_left hY]
  exact (retained_finite_series η F hF R Y hY).symm

def retainedOriginal (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
    finiteAnnularColumn χ.inverse
      (paperRadialFourier (CompletedHeight.normTwistedSource W t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

theorem actual_original_retained_approximation (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(χ : Character),χ.residue≠1 →
        ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
        ∀(X t Z : ℝ),0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            G*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
            C*(χ.modulus.absNorm:ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_deleted_discarded_negligible a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro χ hχ
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_retained_reflection χ hχ
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro X t Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  let Wt := CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t
  have heWt : (Wt : ℝ→ℂ)=CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : DecayTwo (paperRadialFourier (CompletedHeight.normTwistedSource W t)) := by
    rw [←heWt]
    exact reflected_decayTwo Wt
  have hret : retainedOriginal χ ψ W X (Z^(xi/2)) t=
      ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(retainedWeight (Z^(xi/2)) x:ℂ)*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
    unfold retainedOriginal
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro H
    rw [finiteAnnularColumn_eq _ _ hF _ _
      (dual_scale_bounds S D hS (Finset.mem_powerset.mp hD) H _ X _ hQ hX hcap').1]
  have hsource := heq Wt X (Z^(xi/2)) hX
  dsimp only at hsource
  rw [heWt] at hsource
  rw [polynomial_twisted_source χ W X t hX,hsource,←hret]
  rw [mul_add,add_sub_cancel_left,norm_mul,hG,one_mul]
  have hb := (hCb S hS ψ ψ.inverse χ.inverse t _ X Z hZ hQ hX hcap').2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hε.le

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI
