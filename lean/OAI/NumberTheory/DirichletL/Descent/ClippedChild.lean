import OAI.NumberTheory.DirichletL.Descent.ClippedUniform
import OAI.NumberTheory.DirichletL.Descent.SecondCellPhysical
import OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
open InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def secondChildHeight (right:Bool)(t:Ambient (Fin 6)):ℝ :=
  if right then profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 5
  else -profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 4

theorem second_child_height_budget (J:ℕ)(right:Bool)(t:Ambient (Fin 6)):
    (1+‖secondChildHeight right t‖)^J≤tripleHeight J t.1*coordinateHeight J t.2:=by
  cases right
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 4 t‖) (inheritedLeft_bound 4 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,Bool.false_eq_true,ite_false,norm_neg,
      second_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 5 t‖) (inheritedRight_bound 5 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,ite_true,second_inherited_right_eq,norm_neg,
      ambientWeight,tripleHeight,coordinateHeight] using h

theorem canonical_actual_child_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z X F E:ℝ)(d:BlockIndex)(right:Bool)(t:Ambient (Fin 6)),
      1<Z→0<X→scales d 0*scales d 2≤b*X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (secondChildHeight right t)) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤
        C*E*(tripleHeight (2*J) t.1*coordinateHeight (2*J) t.2):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,he⟩:=canonical_clipped_uniform W lo hi b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩:=he J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z X F E d right t hZ hX hgeom hE hmoment
  obtain ⟨hc1,hcb⟩:=second_cell_clipping_ratio Z X b d hZ hX hb hgeom
  have hz:0<Z:=zero_lt_one.trans hZ
  exact (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    _ (secondChildHeight right t) _ Z F E hc1 hcb (Real.rpow_pos_of_pos hz _) hE hmoment).trans
      (mul_le_mul_of_nonneg_left (second_child_height_budget (2*J) right t) (mul_nonneg hC.le hE))

end SevenEighths.InverseMoment

end

end OAI
