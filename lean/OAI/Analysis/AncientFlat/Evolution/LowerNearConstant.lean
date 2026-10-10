import OAI.Analysis.AncientFlat.Regularity.LowerUnitInterpolation
import OAI.Analysis.AncientFlat.Evolution.NearConstant

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem lower_near_constant_fourth (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ δ C : ℝ, 0<δ ∧ δ≤1 ∧ 0<C ∧ ∀ (A : ℝ), κ≤A → A≤K →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ) (c : Coefficients V),
      HolderBound α (cylinder 8) a K → HolderBound α (cylinder 8) b K →
      (∀ j, HolderBound α (cylinder 8) (c j) K) →
      (∀ p∈cylinder 2, ‖A-a p‖≤δ) →
      ∀ (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈cylinder 8, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α (cylinder 8) u ut M) →
      HolderBound α (cylinder 8) (fun p => f p.2 p.1) F →
      (∀ p∈cylinder 8, ‖u p.2 p.1‖≤U) →
      (∀ p∈cylinder 8, ∀ q∈cylinder 8,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u q.2) q.1‖≤H*pdist p q^α) →
      (∀ p∈cylinder 8, ut p.2 p.1+(a p:ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1+spatialLower c u p=f p.2 p.1) →
      HolderBound α (cylinder 1) (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) (θ*H+C*(F+U)) := by
  obtain ⟨δ,C0,hδ,hδ1,hC0,HS⟩ := near_constant_fourth (V := V) α κ K (θ/2) hα hα1 hκ hK (by linarith)
  let ε := θ/(12*C0*(1+K))
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨C1,hC1,HL⟩ := unit_lower_interpolation (V := V) α K ε hα hα1 hK hε
  let C := C0*(2+6*K*C1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro A hκA hAK a b c ha hb hc hosc u ut f F U H hF hU hH hs hd hj hf hu hh he
  have h48 : (cylinder 4 : Set (V × ℝ))⊆cylinder 8 := cylinder_mono (by norm_num) (by norm_num)
  have hL := HL a b c u ut f F U H hF hU hH hs hd ha.1 hb.1 (fun j => (hc j).1) hf.1 hu hh he
  let L := ε*H+C1*(F+U)
  have hL0 : 0≤L := by dsimp [L]; positivity
  have hLower := lower_holder hK hL0 c u (fun j => (hc j).restrict h48) (fun j => hL (j.val+1) (by omega))
  let g := fun t x => f t x-spatialLower c u (x,t)
  have hg : HolderBound α (cylinder 4) (fun p => g p.2 p.1) (F+6*K*L) := by
    simpa only [g,sub_eq_add_neg] using (hf.restrict h48).add hLower.neg
  have Hj : ∃ M, 0≤M ∧ JetBound α (cylinder 4) u ut M := by
    obtain ⟨M,hM,hj⟩ := hj
    exact ⟨M,hM,(fun j hj' => (hj.1 j hj').restrict h48),hj.2.restrict h48⟩
  have HE := HS A hκA hAK a b (ha.restrict h48) (hb.restrict h48) hosc u ut g
    (F+6*K*L) U H (by positivity) hU hH hs (fun p hp => hd p (h48 hp)) Hj hg
    (fun p hp => hu p (h48 hp)) (fun p hp q hq => hh p (h48 hp) q (h48 hq))
    (fun p hp => by have h := he p (h48 hp); dsimp [g]; linear_combination h)
  apply HE.mono
  have hεE : 12*C0*(1+K)*ε=θ := by dsimp [ε]; field_simp
  have hsmall : 6*C0*K*ε≤θ/2 := by nlinarith [mul_pos hC0 hε]
  have hCU : 0≤C0*(F+U) := by positivity
  dsimp [L,C]
  nlinarith [mul_le_mul_of_nonneg_right hsmall hH]
end ParabolicLowerOrder

end

end OAI
