import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerClipping
import OAI.NumberTheory.DirichletL.Descent.ClippedUniform

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic CompletedGauss
namespace SevenEighths.InverseInitialEnergyCallerUniform
open InverseMoment InverseInitialClippedColumns InverseInitialProfile
local notation "Eis"=>ActualEisensteinCubic.O

theorem initial_height_bound (J:ℕ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (h:ℝ)(hh:h = -leftHeight z ∨ h=rightHeight z) :
    (1+‖h‖)^(2*J)≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
  have hb := child_height_moment_bound (2*J) z
  have hl : 1≤(1+‖leftHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (leftHeight z)])
  have hr : 1≤(1+‖rightHeight z‖)^(2*J) := one_le_pow₀ (by linarith [norm_nonneg (rightHeight z)])
  rw [show 2*(2*J)=4*J by omega] at hb
  rcases hh with rfl|rfl
  · rw [norm_neg]
    exact (le_mul_of_one_le_right (by positivity) hr).trans hb
  · exact (le_mul_of_one_le_left (by positivity) hl).trans hb

theorem initial_raw_uniform
    (W:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo b)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)(D:Ideal Eis→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z N F E:ℝ)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(h:ℝ),1<Z→0≤E→
      (h = -leftHeight z ∨ h=rightHeight z)→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 N)) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest W h) (Z^N) Z F≤C*E*(tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,huniform⟩ := canonical_clipped_uniform W lo b b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩ := huniform J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh hm
  by_cases hne:(freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc1,hcb⟩ := freshColumns_clipping_range p hp pool W lo b Z N hZ hb hs hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc1 hcb (by positivity) hE hm).trans
    exact mul_le_mul_of_nonneg_left (initial_height_bound J z h hh) (mul_nonneg hC.le hE)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h he,mul_zero,norm_zero,zero_pow (by omega : (2:ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [tripleHeight,coordinateHeight]
    positivity

end SevenEighths.InverseInitialEnergyCallerUniform

end

end OAI
