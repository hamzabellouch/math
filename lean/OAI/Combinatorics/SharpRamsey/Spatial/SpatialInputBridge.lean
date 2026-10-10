import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialCover
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPrepared

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real Filter SpatialLearning GreedyPreparation PreparedProjectiveGeometry
open scoped Classical BigOperators Topology NNReal
noncomputable section

theorem actual_prepared_input (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (U S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) (Fin 4→ZMod q)))),
    S⊆U → S.Nonempty → T.Nonempty → S.card≤T.card →
    ∀ (P g b τ : ℝ) (p : ℕ),0≤τ →
    σ^δ≤P → P≤σ/40 → g≤σ/2+C → 0<p → (p:ℝ)≤σ^2 →
    (S.card:ℝ)=exp (3*σ/2+g) →
    (q:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card →
    (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/q →
    (∃ W : Submodule (ZMod q) (Fin 4→ZMod q),Module.finrank (ZMod q) W=3 ∧
      (S.card:ℝ)/50≤(S∩planePoints W).card) ∨
    (∃ (S' : Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
      (planes : List (Submodule (ZMod q) (Fin 4→ZMod q))),
      S'⊆S ∧ S'.Nonempty ∧ S.card≤2*S'.card ∧
      (planes.length:ℝ)≤exp (σ/2-2*g/15) ∧
      (∀ W∈planes,Module.finrank (ZMod q) W=3) ∧
      Input U S'.card planePoints (sized S' planePoints planes)
        σ P g (b+log 2) (2*τ) (Real.toNNReal ((q:ℝ)/S'.card)) p S') := by
  filter_upwards [prepared_input δ C hδ] with σ hprep
  intro q _ hq hx U S T hSU hS hT hST P g b τ p hτ hP hPu hgu hp hpu hN hprod hsp
  rcases hprep q hq hx S hS P g p hP hPu hgu hp hpu hN with hh|hh
  · exact Or.inl hh
  · obtain ⟨S',planes,hsub,hn,hhalf,hJ,hrank,hcell,D₀,D₁,hD₀,hD₁,hrad,hstrong⟩ := hh
    right
    refine ⟨S',planes,hsub,hn,hhalf,hJ,hrank,?_⟩
    have hc : S'.card≤S.card := card_le_card hsub
    have hc' : (S'.card:ℝ)≤S.card := by exact_mod_cast hc
    have hh' : (S.card:ℝ)≤2*S'.card := by exact_mod_cast hhalf
    have hqp : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have hns : (0:ℝ)<S'.card := by exact_mod_cast card_pos.mpr hn
    have he : exp (-(b+log 2))=exp (-b)/2 := by
      rw [neg_add,exp_add,exp_neg (log 2),exp_log (by norm_num : (0:ℝ)<2)]
      ring
    have hmon : Incidence.incidenceCount S' T≤Incidence.incidenceCount S T := by
      apply sum_le_sum
      intro y _
      exact card_le_card (filter_subset_filter _ hsub)
    have hsp' : (Incidence.incidenceCount S' T:ℝ)≤(2*τ)*(S'.card:ℝ)*T.card/q := by
      calc
        _ ≤ (Incidence.incidenceCount S T:ℝ) := by exact_mod_cast hmon
        _ ≤ τ*(S.card:ℝ)*T.card/q := hsp
        _ ≤ τ*(2*S'.card)*T.card/q := by gcongr
        _ = _ := by ring
    have hcq : (Real.toNNReal ((q:ℝ)/S'.card):ℝ)=(q:ℝ)/S'.card :=
      Real.coe_toNNReal _ (by positivity)
    unfold Input
    rw [sized_planes]
    refine ⟨hsub.trans hSU,rfl,hc'.trans hN.le,rfl,hcell,⟨T,hT,hc.trans hST,?_,?_⟩,
      D₀,D₁,hD₀,hD₁,?_,?_⟩
    · have ht : 0≤(T.card:ℝ) := Nat.cast_nonneg _
      rw [Nat.card_eq_fintype_card,ZMod.card,he]
      nlinarith [mul_le_mul_of_nonneg_right hh' ht]
    · simpa only [Nat.card_eq_fintype_card,ZMod.card] using hsp'
    · simpa only [hcq,hx] using hrad
    · simpa only [hcq,hx] using hstrong

end
end SharpLogRamsey.SpatialPublic

end

end OAI
