import OAI.MeasureTheory.Falconer.Estimates.EndpointScaleInputs
import OAI.MeasureTheory.Falconer.Estimates.UniformScaleCombination

namespace OAI

/-! The actual scale-product step on dyadic endpoint configurations. Both
outputs stay in the same fixed quarter chart, with the same slope interval. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem quarter_endpoint_scale_product {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ C.image (List.take a)) {s t K KP m M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hKP : 0 ≤ KP) (hm : 0 < m) (hM : 0 < M)
    (hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) t KP (quarterEndpointSet Q C c b r))
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ quarterEndpointSet Q C a b p₀,
      m ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-a+2)) s K (V x) ∧
      ∀ l ∈ V x, |l 0| ≤ 1/2 ∧ TubeIncident (1/(2:ℝ)^(b-a+2)) x l) :
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    let ρ := 1/(2:ℝ)^(c-a+2)
    let δ' := 1/(2:ℝ)^(b-c+2)
    let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
    let Jg := Nat.log 2 (P.biUnion V).card+1
    ∃ L E F w : ℝ, 0 < L ∧ L ≤ 20*(Jg:ℝ)^2 ∧ E = 8*(Jv:ℝ)*(Jg:ℝ) ∧
      F = 2*E*M/m ∧ 0 < w ∧ ∃ R ⊆ D, R.Nonempty ∧ (D.card:ℝ) ≤ L*(R.card:ℝ) ∧
      ∃ U : Space 2 → Finset (Space 2),
        (∀ z ∈ R, w/(2*(Jg:ℝ)) ≤ ((U z).card:ℝ) ∧ ((U z).card:ℝ) ≤ 2*w ∧
          InBoundedLineChart (U z) ∧ FiniteSeparatedAt ρ (U z) ∧
          NormalizedFiniteBallBound ρ s ((2*(K*7^s)*(Jv:ℝ))*L) (U z) ∧
          ∀ l ∈ U z, |l 0| ≤ 1/2 ∧ TubeIncident ρ z l) ∧
        ∀ r ∈ prefixChildren C a c p₀, quarterEndpointPoint Q a p₀ r ∈ R →
          ∃ j : ℕ, ∃ P' ⊆ quarterEndpointSet Q C c b r,
            P'.Nonempty ∧ ((quarterEndpointSet Q C c b r).card:ℝ) ≤ (F*(Jg:ℝ))*(P'.card:ℝ) ∧
            (∀ x ∈ P', |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4) ∧ FiniteSeparatedAt δ' P' ∧
            NormalizedFiniteBallBound δ' t ((KP*F)*(Jg:ℝ)) P' ∧
            ∃ T : Space 2 → Finset (Space 2),
              (∀ x ∈ P', (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
                FiniteSeparatedAt δ' (T x) ∧
                NormalizedFiniteBallBound δ' s (2*(((K*F)*3^s)*7^s)*(Jg:ℝ)) (T x) ∧
                (∀ l ∈ T x, |l 0| ≤ 1/2 ∧ TubeIncident δ' x l) ∧
                (m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j) ≤ ((T x).card:ℝ) ∧
                ((T x).card:ℝ) ≤ M/(2:ℝ)^j) ∧
              (((R.biUnion U).card:ℝ)/(w/(2*(Jg:ℝ))))*
                (((P'.biUnion T).card:ℝ)/((m/(2*E))/(2*(Jg:ℝ)*(2:ℝ)^j))) ≤
                  (43264*(Jv:ℝ)*(Jg:ℝ)^3)*(((P.biUnion V).card:ℝ)/m) := by
  let P := quarterEndpointSet Q C a b p₀
  let D := quarterEndpointSet Q C a c p₀
  let δ := 1/(2:ℝ)^(b-a+2)
  let ρ := 1/(2:ℝ)^(c-a+2)
  let Jv := Nat.log 2 (∑ x ∈ P, (V x).card)+1
  let Jg := Nat.log 2 (P.biUnion V).card+1
  obtain ⟨q,hD,himage,hnear,hsmall,hsep,hlocal,hfibers,hδ,hρ,hρ1,hδρ⟩ :=
    quarter_endpoint_scale_inputs hac hcb Q hQ C hC hbN p₀ hp₀ hball
  obtain ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hmass,U,hU,hUslope,hcells⟩ :=
    uniform_scale_combination hδ hρ hρ1 hδρ hs hK hKP hm hM P D V q hD
      (show D ⊆ P.image q from himage.subset) hnear hsmall hsep hlocal hV
  refine ⟨L,E,F,w,hL,hLb,hE,hF,hw,R,hRD,hR,hmass,U,?_,?_⟩
  · intro z hz
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hU z hz
    refine ⟨hlo,hhi,hch,hsp,hb,?_⟩
    intro l hl
    exact ⟨hUslope (fun x hx => lineGridRound_dyadic_half (c-a+1) hx) z hz l hl,hinc l hl⟩
  · intro r hr hrR
    obtain ⟨j,P',hsub,hP',hcount,hch,hsp,hb,T,hT,hproduct,hTslope⟩ := hcells _ hrR
    have heq := hfibers r hr
    have hcard : ((P.filter fun x => q x = quarterEndpointPoint Q a p₀ r).card:ℝ) =
        ((quarterEndpointSet Q C c b r).card:ℝ) := by
      rw [← heq,Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity) _ _)]
    rw [heq] at hsub
    rw [hcard] at hcount
    have hmesh : δ/(4*ρ) = 1/(2:ℝ)^(b-c+2) := dyadic_endpoint_local_mesh hac hcb
    rw [hmesh] at hsp hb hT
    refine ⟨j,P',hsub,hP',hcount,hch,hsp,hb,T,?_,hproduct⟩
    intro x hx
    obtain ⟨hne,hchart,hseparated,hregular,hinc,hlo,hhi⟩ := hT x hx
    refine ⟨hne,hchart,hseparated,hregular,?_,hlo,hhi⟩
    intro l hl
    refine ⟨hTslope ?_ x hx l hl,hinc l hl⟩
    intro u hu
    rw [hmesh]
    exact lineGridRound_dyadic_half (b-c+1) hu

end Falconer

end OAI
