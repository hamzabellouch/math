import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGates

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma actual_profile_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X b : ℝ) (hX : 0<X)
    (hW : ∀y,W₁ y≠0 → y≤b)
    (hgeom : b*X<primeProductNorm p x.common*primeProductNorm p x.overlap) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X=0 := by
  rw [actualSecondProfileRow_eq_whole]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  have hzero : W₁ (primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N/X)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hX).mp (hW _ hn)
    have hlo := le_mul_of_one_le_right
      (mul_nonneg (primeProductNorm_pos p hp x.common).le (primeProductNorm_pos p hp x.overlap).le)
      (primeProductNorm_ge_one p hp N)
    linarith
  simp [secondNormProfile,secondActualNorms,hzero]

lemma wholeRow_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X Y b : ℝ) (hX : 0<X) (hW : ∀y,W y≠0 → y≤b)
    (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)
    (hgeom : b*X<primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x=0 := by
  rw [wholeRow_eq]
  have hh := actual_profile_zero_of_geometry p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
    (slots\J) (slots\J) (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
    (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a W W rowMajorant Y X b hX hW hgeom
  rw [hh,mul_zero]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
def geometrySource {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    Finset (MarkedSecondSource ι Jo Jn) :=
  source.filter (fun x=>primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X)

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_gate {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    ∀x∈geometrySource p source b X,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X :=
  fun _x hx=>(Finset.mem_filter.mp hx).2

lemma original_retained_geometry_sum
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (MarkedSecondSource ι Jo 0)) (w : MarkedSecondSource ι Jo 0→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X Y b : ℝ)
    (hX : 0<X) (hW : ∀y,W y≠0 → y≤b) (ray : SecondRayIndex) :
    (∑x∈source,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x)=
    ∑x∈geometrySource p source b X,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x := by
  rw [geometrySource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hg₀
  · rfl
  · rw [wholeRow_zero_of_geometry p hp hcop hg extra pool negative Ψ m slots J lists a W X Y b hX hW
      ray x (lt_of_not_ge hg₀),mul_zero]

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
