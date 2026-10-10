import Mathlib
import OAI.Probability.SKGap.Posterior.BufferedPosteriorDirection

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static
universe u

theorem buffered_posterior_covariance {j K B Aroot ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hB : 0≤B) (hA : 1≤Aroot) (hc : 0<c)
    (hr₀ : 0<r₀) (hρ : 0<ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤Aroot)
    (hbuffer : (K+4*j)*(2*ρ)<r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε)
    (himplicit : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
      c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (habsorb : (|j| *|literalSizeBudget j c R K
        (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
      ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2)
    : ∃A : ℕ→ℝ,(∀k,1≤A k) ∧ ∀m:ℕ,∀δ:ℝ,0<δ→
      2<(m:ℝ)*ρ^2/4→2*(2*m:ℕ)*δ≤1→∀W C:ℝ,0≤W→0≤C→
      ∀(Ω : Type u) (n : Ω→ℕ) (J : ∀b,Interaction (n b))
      (h : ∀b,Fin (n b)→ℝ),
      (∀b,0<n b)→(∀b,(J b).IsSymm)→(∀b i,J b i i=0)→
      (∀b k,k<2*m-1→StartedMatrixEvent j K (Real.exp (R/2)) (A k) (c/2) B W C (k+3) (2+2*(k+1)) (J b))→
      (∀b,RecipeMatrixEvent j K (residualCoefficientBudget j 2 (2*m) 0) B W C (2*m+1) (2*(2*m)) (J b))→
      (∀b,¬SKGap.rootBad j Aroot ε c r₀ (J b) (h b))→
      (∀b k,k<2*m-1→4*(residualDerivativeBudget j K B k+residualDerivativeBudget j K B (k+1))≤ρ*Real.sqrt (n b:ℝ))→
      ∃D≥0,∀b (G : Observables (n b)),
        vectorNorm (centeredSpinCovariance (fieldGibbs (J b) (h b)) G)≤
          D*Real.sqrt ((∑x,fieldGibbs (J b) (h b) x*
            (G x-∑y,fieldGibbs (J b) (h b) y*G y)^2)+
            varianceEnergy (fieldGibbs (J b) (h b)) G) := by
  obtain ⟨A,hA',hs⟩:=buffered_root_posterior_direction.{u} hj hK hB hA hc hr₀ hρ hε
    hAR hbuffer hR hsmall himplicit habsorb
  refine ⟨A,hA',?_⟩
  intro m δ hδ hm hδm W C hW hC Ω n J h hn hJ hdiag hstarted hevent hbad hdim
  let Λ:=Σb:Ω,{e : Fin (n b)→ℝ //vectorNorm e≤1}
  obtain ⟨r,hr,D,hD,hw⟩:=hs m δ hδ hm hδm W C hW hC Λ (fun a=>n a.1)
    (fun a=>J a.1) (fun a=>h a.1) (fun a=>a.2.1)
    (fun a=>hn a.1) (fun a=>hJ a.1) (fun a=>hdiag a.1) (fun a=>a.2.2)
    (fun a=>hstarted a.1) (fun a=>hevent a.1) (fun a=>hbad a.1) (fun a=>hdim a.1)
  refine ⟨D,hD,?_⟩
  intro b G
  apply posterior_vectorNorm_le_of_unit_dot _ (mul_nonneg hD (Real.sqrt_nonneg _))
  intro e he
  exact weak_direction_center _ G (sum_fieldGibbs _ _) (r ⟨b,e,he⟩) e (hw ⟨b,e,he⟩)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open Filter Topology
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary Static

theorem posterior_buffer_exists (j K c r₀ R ε : ℝ)
    (hc : 0<c) (hr₀ : 0<r₀) (hR : 0<R) (hε : 0<ε) :
    ∃ρ : ℝ,0<ρ ∧
      (K+4*j)*(2*ρ)<r₀ ∧
      (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤R ∧
      (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤ε ∧
      (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ)≤
        c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)) ∧
      (|j| *|literalSizeBudget j c R K
          (KernelExpr.dr (KernelExpr.atom 0 0 false))|)*
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*(2*ρ))≤(1:ℝ)/2 := by
  have small (a b : ℝ) (hb : 0<b) : ∀ᶠ ρ : ℝ in 𝓝[>] 0,a*(2*ρ)<b := by
    have H : Tendsto (fun ρ : ℝ => a*(2*ρ)) (𝓝[>] 0) (𝓝 (0:ℝ)) := by
      have C : ContinuousAt (fun ρ : ℝ => a*(2*ρ)) 0 := by fun_prop
      simpa using C.tendsto.mono_left nhdsWithin_le_nhds
    exact H.eventually_lt_const hb
  let q := (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))
  let d := c/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))
  have hd : 0<d := by dsimp [d]; positivity
  let z := |j| *|literalSizeBudget j c R K
    (KernelExpr.dr (KernelExpr.atom 0 0 false))|
  have hp : ∀ᶠ ρ : ℝ in 𝓝[>] 0,0<ρ := self_mem_nhdsWithin
  have H : ∀ᶠ ρ : ℝ in 𝓝[>] 0, 0<ρ ∧ (K+4*j)*(2*ρ)<r₀ ∧
      q*(2*ρ)<R ∧ (3*Real.exp (R/2)+2)*(q*(2*ρ))<ε ∧
      q*(2*ρ)<d ∧ z*(q*(2*ρ))<(1:ℝ)/2 := by
    filter_upwards [hp,small (K+4*j) r₀ hr₀,small q R hR,
      small ((3*Real.exp (R/2)+2)*q) ε hε,small q d hd,
      small (z*q) ((1:ℝ)/2) (by norm_num)] with ρ hp h1 h2 h3 h4 h5
    exact ⟨hp,h1,h2,by simpa only [mul_assoc] using h3,h4,
      by simpa only [mul_assoc] using h5⟩
  obtain ⟨ρ,hp,h1,h2,h3,h4,h5⟩:=H.exists
  exact ⟨ρ,hp,h1,h2.le,h3.le,h4.le,h5.le⟩

theorem posterior_selection_parameters {ρ : ℝ} (hρ : 0<ρ) :
    ∃ m : ℕ, 0 < m ∧ ∃ δ : ℝ, 0 < δ ∧ 2 <(m:ℝ)*ρ^2/4 ∧
      2*(2*m:ℕ)*δ≤1 := by
  obtain ⟨m,hm⟩:=exists_nat_gt ((8:ℝ)/ρ^2)
  have hp : 0<(m:ℝ) := lt_trans (div_pos (by norm_num) (sq_pos_of_pos hρ)) hm
  have hd : 0<4*(m:ℝ)+1 := by positivity
  have hmul : 8<(m:ℝ)*ρ^2 := (div_lt_iff₀ (sq_pos_of_pos hρ)).mp hm
  refine ⟨m,by exact_mod_cast hp,(4*(m:ℝ)+1)⁻¹,inv_pos.mpr hd,by nlinarith,?_⟩
  have H : 4*(m:ℝ)/(4*(m:ℝ)+1)≤1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  simpa only [Nat.cast_mul,Nat.cast_ofNat,div_eq_mul_inv,show (2:ℝ)*(2*(m:ℝ))=4*m by ring] using H

end SKGapCutoff.Recipe

end
end

end OAI
