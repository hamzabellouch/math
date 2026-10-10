import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.UniformSupports

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma endpoint_error_scale {x b κ δ H L S C₀ : ℝ}
    (hx : 1≤x) (hb : 0≤b) (hC₀ : 0≤C₀)
    (hκ : x^(4*b)≤κ) (hδ : δ≤κ*x^(-2*b))
    (hH : L-H≤δ) (hS : S*exp (-L)≤C₀) :
    exp (-κ)+(L-H+S*exp (-L))/(κ*(1/50))≤
      (51+50*C₀)*x^(-2*b) := by
  have hx0 : 0<x := by linarith
  have hp : 0<x^(2*b) := rpow_pos_of_pos hx0 _
  have hk : x^(2*b)≤κ := (rpow_le_rpow_of_exponent_le hx (by linarith)).trans hκ
  have hk0 : 0<κ := hp.trans_le hk
  have hi : 1/κ≤x^(-2*b) := by
    have hh:=one_div_le_one_div_of_le hp hk
    simpa only [neg_mul,rpow_neg hx0.le,one_div] using hh
  have he : exp (-κ)≤1/κ := by
    rw [exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le hk0
      (show κ≤exp κ by linarith [add_one_le_exp κ]))
  have hd : δ/κ≤x^(-2*b) := (div_le_iff₀ hk0).mpr (by simpa only [mul_comm κ] using hδ)
  have hsn : (L-H+S*exp (-L))/(κ*(1/50))≤50*(δ/κ)+50*C₀*(1/κ) := by
    calc
      _ ≤ (δ+C₀)/(κ*(1/50)) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ x^(-2*b)+(50*(δ/κ)+50*C₀*(1/κ)) := add_le_add (he.trans hi) hsn
    _ ≤ x^(-2*b)+(50*x^(-2*b)+50*C₀*x^(-2*b)) := by gcongr
    _ = _ := by ring

variable {A B : Type*} [Fintype A] [Fintype B]

theorem actual_endpoint_errors (p : Law (A×B)) (S : Finset (A×B))
    (DA : Finset A) (DB : Finset B)
    (hs : ∀ z,z∉S→p.mass z=0)
    (ha : ∀ a,a∉DA→p.fst.mass a=0) (hb : ∀ b,b∉DB→p.snd.mass b=0)
    (MA MB L κ x β δ C₀ : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (hA : (DA.card:ℝ)≤MA) (hB : (DB.card:ℝ)≤MB)
    (hx : 1≤x) (hβ : 0≤β) (hC₀ : 0≤C₀)
    (hκ : x^(4*β)≤κ) (hδ : δ≤κ*x^(-2*β))
    (hdef : L-entropy p≤δ) (hS : (S.card:ℝ)*exp (-L)≤C₀) :
    p.fst.event (univ.filter (fun a=>¬goodFirst p MA L κ (1/50) a))≤(51+50*C₀)*x^(-2*β) ∧
    p.snd.event (univ.filter (fun b=>¬goodSecond p MB L κ (1/50) b))≤(51+50*C₀)*x^(-2*β) := by
  have hκ0 : 0<κ := (rpow_pos_of_pos (by linarith : 0<x) (4*β)).trans_le hκ
  have he:=endpoint_error_scale hx hβ hC₀ hκ hδ hdef hS
  exact ⟨(badFirst_mass p S hs DA ha MA L κ (1/50) hMA hA hκ0 (by norm_num)).trans he,
    (badSecond_mass p S hs DB hb MB L κ (1/50) hMB hB hκ0 (by norm_num)).trans he⟩

end
end SharpLogRamsey.Selection

end

end OAI
