import OAI.MeasureTheory.Falconer.Measures.EndpointScaleProduct
import OAI.MeasureTheory.Falconer.Recursion.ProfileEndpointBound
import OAI.MeasureTheory.Falconer.Recursion.ProfileStepBudget

namespace OAI

/-! The actual geometric scale product with uniform depth and pencil budgets.
Both outputs retain their original dyadic endpoints and half-slope chart. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_budgeted_scale_product {N a b c : ℕ}
    (hac : a ≤ c) (hcb : c ≤ b) (Q : DyadicCube 2) (hQ : Q.side = 1)
    (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N)
    (p₀ : CellPath 2) (hp₀ : p₀ ∈ C.image (List.take a))
    {s W m : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hW : 1 ≤ W) (hm : 0 < m)
    (V : Space 2 → Finset (Space 2))
    (hV : QuarterPencilData (1/(2:ℝ)^(b-a+2)) s W m (quarterEndpointSet Q C a b p₀) V) :
    let H : ℝ := (4*(N+2)+11:ℕ)
    let U0 := profileStepBudget H 1 W
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    ∃ R ⊆ D, R.Nonempty ∧ (D.card:ℝ) ≤ (20*H^2)*(R.card:ℝ) ∧
      ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ U : Space 2 → Finset (Space 2),
        QuarterPencilData (1/(2:ℝ)^(c-a+2)) s U0 m₀ R U ∧
        ∀ r ∈ prefixChildren C a c p₀, quarterEndpointPoint Q a p₀ r ∈ R →
          ∃ P' ⊆ quarterEndpointSet Q C c b r, P'.Nonempty ∧
            ((quarterEndpointSet Q C c b r).card:ℝ) ≤ (16*W*H^3)*(P'.card:ℝ) ∧
            ∃ m₁ : ℝ, 0 < m₁ ∧ ∃ T : Space 2 → Finset (Space 2),
              QuarterPencilData (1/(2:ℝ)^(b-c+2)) s U0 m₁ P' T ∧
              (((R.biUnion U).card:ℝ)/m₀)*(((P'.biUnion T).card:ℝ)/m₁) ≤
                (43264*H^4)*(((P.biUnion V).card:ℝ)/m) := by
  let H : ℝ := (4*(N+2)+11:ℕ)
  let P := quarterEndpointSet Q C a b p₀
  let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hδ : 0 ≤ 1/(2:ℝ)^(b-a+2) := by positivity
  obtain ⟨_,hchart,hsep⟩ := quarterEndpointSet_geometry Q hQ C hC (hac.trans hcb) hbN p₀
  have hmesh : 1/(2:ℝ)^(N+2) ≤ 1/(2:ℝ)^(b-a+2) := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlogs := separated_pencil_configuration_logs (N+2) P V
    (fun x hx => ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩)
    (fun x hx y hy hxy => hmesh.trans (hsep x hx y hy hxy))
    (fun x hx => ⟨(hV x hx).2.2.1,
      fun u hu v hv huv => hmesh.trans ((hV x hx).2.2.2.1 u hu v hv huv)⟩)
  have hJvH : (Jv:ℝ) ≤ H := by dsimp [Jv,H]; exact_mod_cast hlogs.1
  have hJgH : (Jg:ℝ) ≤ H := by dsimp [Jg,H]; exact_mod_cast hlogs.2
  have hJv : 0 < (Jv:ℝ) := by dsimp [Jv]; positivity
  have hJg : 0 < (Jg:ℝ) := by dsimp [Jg]; positivity
  have hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) 0 1 (quarterEndpointSet Q C c b r) := by
    intro r hr z ρ hρ hρ1
    simp only [Real.rpow_zero,mul_one,one_mul]
    exact Nat.cast_le.mpr (Finset.card_filter_le _ _)
  obtain ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hRcount,U,hU,hcells⟩ :=
    quarter_endpoint_scale_product hac hcb Q hQ C hC hbN p₀ hp₀ hs hW
      (by norm_num) hm (mul_pos (zero_lt_one.trans_le hW) hm) hball V
      (fun x hx => ⟨(hV x hx).1,(hV x hx).2.1,(hV x hx).2.2.2.2.1,(hV x hx).2.2.2.2.2⟩)
  have hE0 : 0 < E := by rw [hE]; positivity
  have hFE : F = 2*E*W := by rw [hF]; field_simp
  obtain ⟨hLH,_,_,hcoarse,hfine,hpoint,hratio,hprod⟩ :=
    uniform_scale_cost_bounds hJv.le hJg.le (zero_le_one.trans hH) hJvH hJgH hL.le hLb hE hFE
      hW0 (by norm_num : (0:ℝ) ≤ 1) hW0 hs1
  obtain ⟨_,hsizeC,hballC,hballF,hsizeF,_,_⟩ := profile_step_budget_bounds (G := 1) hH (by norm_num) hW
  have hpoint' : F*(Jg:ℝ) ≤ 16*W*H^3 := by simpa only [one_mul,mul_one] using hpoint
  have hfine' : 2*(((W*F)*3^s)*7^s)*(Jg:ℝ) ≤ 672*W^2*H^3 := by
    convert hfine using 1; ring
  let m₀ := w/(2*(Jg:ℝ))
  have hm₀ : 0 < m₀ := by dsimp [m₀]; positivity
  have hratioC : 2*w ≤ profileStepBudget H 1 W*m₀ := by
    apply (div_le_iff₀ hm₀).mp
    rw [coarse_pencil_size_ratio hw hJg]
    exact (mul_le_mul_of_nonneg_left hJgH (by norm_num)).trans hsizeC
  refine ⟨R,hRD,hR,hRcount.trans (mul_le_mul_of_nonneg_right hLH (Nat.cast_nonneg _)),
    m₀,hm₀,U,?_,?_⟩
  · intro z hz
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hU z hz
    exact ⟨hlo,hhi.trans hratioC,hch,hsp,
      normalizedFiniteBallBound_mono_constant (by positivity) (hcoarse.trans hballC) hb,hinc⟩
  · intro r hr hrR
    obtain ⟨j,P',hPsub,hP,hPcount,_,_,_,T,hT,hproduct⟩ := hcells r hr hrR
    let m₁ := (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j)
    have hm₁ : 0 < m₁ := by dsimp [m₁]; positivity
    have hratioF : (W*m)/(2:ℝ)^j ≤ profileStepBudget H 1 W*m₁ := by
      apply (div_le_iff₀ hm₁).mp
      rw [rescaled_pencil_size_ratio hm hE0 hJg]
      have he : (W*m)/m = W := by field_simp
      rw [he]
      exact hratio.trans hsizeF
    refine ⟨P',hPsub,hP,hPcount.trans
      (mul_le_mul_of_nonneg_right hpoint' (Nat.cast_nonneg _)),m₁,hm₁,T,?_,?_⟩
    · intro x hx
      obtain ⟨_,hch,hsp,hb,hinc,hlo,hhi⟩ := hT x hx
      exact ⟨hlo,hhi.trans hratioF,hch,hsp,
        normalizedFiniteBallBound_mono_constant (by positivity) (hfine'.trans hballF) hb,hinc⟩
    · exact hproduct.trans (mul_le_mul_of_nonneg_right hprod (by positivity))

end Falconer

end OAI
