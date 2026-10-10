import Mathlib
import OAI.Combinatorics.KMedian.Geometry.TimeAdvance
import OAI.Combinatorics.KMedian.Process.SourceGenerator
import OAI.Combinatorics.KMedian.Process.AveragedGenerator

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic GeneratorAverage GraphMoments
variable {I : Type*} [DecidableEq I] [Fintype I]

theorem averaged_source_drift (Δ : ℕ) (S : Finset I) {g x pHat ζ b : ℝ}
    (d N : I → ℝ) (q : I → I → ℝ)
    (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : mass g S ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hq0 : ∀ h i, 0 ≤ q h i) (hq1 : ∀ h i, q h i ≤ 1)
    (hsum : ∀ i, ∑ h, q h i=Δ)
    (hp0 : 0 ≤ pHat) (hp1 : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i ∈ S, ∀ t ∈ S, q t i < 1 → N i*(1-pHat*q t i) ≤ d i+d t)
    (htaper : ∀ h i, 0 < q h i → min b (d h) ≤ d i+(1-pHat*q h i)*N i) :
    ∃ μ : FiniteLaw (I → Finset I),
      (∀ G, 0 < μ.weight G → ∀ i, (G i).card=Δ) ∧
      (∀ h i, μ.expect (fun G => GraphLaw.edge G h i)=q h i) ∧
      (∀ h k i j, i ≠ j → μ.expect (fun G => GraphLaw.edge G h i*GraphLaw.edge G k j)=q h i*q k j) ∧
      (∀ G, 0 < μ.weight G → ∀ h i, q h i=1 → h ∈ G i) ∧
      (∀ G, 0 < μ.weight G → ∀ h i, q h i=0 → h ∉ G i) ∧
      (timeRate x (mass g S)*PhysicalPotential.cost g d S+
        μ.expect (fun G => g*∑ h ∈ relevant (graphActions G) S,
          charge (graphActions G) x g b d S h) ≤
        B x*g*PhysicalPotential.cost g d S+12*ζ*PhysicalPotential.cost g d S) := by
  obtain ⟨μ, hcard, hfirst, hpair, hone, hzero⟩ := GraphLaw.exists_law q Δ hq0 hq1 hsum
  refine ⟨μ, hcard, hfirst, hpair, hone, hzero, ?_⟩
  have hysum : (∑ _i : S, g)=mass g S := by
    simp [mass, mul_comm]
  have hV : (∑ i : S, g*d i)=PhysicalPotential.cost g d S := sum_coe_sort S (fun i => g*d i)
  have hmass : ∀ i : S, (∑ h : (Sᶜ : Finset I), g*q h i)=1-∑ t : S, g*q t i := by
    intro i
    have hh := congrArg (fun z : ℝ => g*z) (hsum i)
    rw [mul_sum, hunit, ← sum_add_sum_compl S] at hh
    rw [sum_coe_sort S (fun t => g*q t i), sum_coe_sort (Sᶜ : Finset I) (fun t => g*q t i)]
    linarith only [hh]
  have ha := averaged_ideal_drift μ (fun i : S => d i) (fun i : S => N i)
    (fun h : (Sᶜ : Finset I) => min b (d h))
    (fun G (h i : S) => GraphLaw.edge G h i)
    (fun G (h : (Sᶜ : Finset I)) (i : S) => GraphLaw.edge G h i)
    (fun (h i : S) => q h i) (fun (h : (Sᶜ : Finset I)) (i : S) => q h i)
    hg hx0 hx1 hysum hy (fun i => hd i) (fun i => hN i)
    (fun h i => hq0 h i) (fun h i => hq1 h i) (fun h i => hq0 h i) (fun h i => hq1 h i)
    hmass hp0 hp1 hζ0 hζ1 he (fun i t => hcomp i i.property t t.property)
    (fun _ => min_le_left _ _) (fun h i => htaper h i)
    (fun h i => hfirst h i) (fun h i => hfirst h i)
    (fun G h i => by unfold GraphLaw.edge; split_ifs <;> norm_num)
    (fun h i t hit => hpair h h i t (fun hh => hit (Subtype.ext hh)))
  dsimp only at ha
  rw [hV] at ha
  have hid : ∀ G, g*(∑ h ∈ relevant (graphActions G) S, charge (graphActions G) x g b d S h)=
      inside g (coefficient x (mass g S))
        (coefficient x (mass g S)*PhysicalPotential.cost g d S+(1-mass g S)*b)
        (fun i : S => d i) (fun (G : I → Finset I) (h i : S) => GraphLaw.edge G h i) G+
      external g (coefficient x (mass g S)) (B x) (PhysicalPotential.cost g d S)
        (fun h : (Sᶜ : Finset I) => min b (d h)) (fun i : S => d i)
        (fun (G : I → Finset I) (h : (Sᶜ : Finset I)) (i : S) => GraphLaw.edge G h i) G := by
    intro G
    rw [source_generator_identity, potential, ← coefficient_eq]
    rfl
  simp_rw [hid]
  exact ha

end MetricKMedian.FixedBatch
end
end

end OAI
