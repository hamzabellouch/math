import OAI.MeasureTheory.Falconer.Estimates.ScalarSumCells
import Mathlib.Combinatorics.Additive.RuzsaCovering

namespace OAI

/-! Ruzsa covering at a fixed scalar resolution, with actual centers
from the original set and an explicit rounding error. -/
namespace Falconer
open scoped Pointwise

theorem scalar_ruzsa_covering {δ K : ℝ} (hδ : 0 < δ)
    (A B : Finset ℝ) (hB : B.Nonempty)
    (hsum : ((scalarCells δ (A+B)).card : ℝ) ≤ K*(scalarCells δ B).card) :
    ∃ F ⊆ A, (F.card : ℝ) ≤ 2*K ∧
      ∀ a ∈ A, ∃ f ∈ F, ∃ b ∈ B, ∃ c ∈ B, |a-(f+(b-c))| ≤ 2*δ := by
  classical
  have hsum' : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
      (2*K)*(scalarCells δ B).card := by
    have hc : ((scalarCells δ A+scalarCells δ B).card : ℝ) ≤
        2*((scalarCells δ (A+B)).card : ℝ) := by exact_mod_cast add_scalarCells_card δ A B
    nlinarith
  obtain ⟨D,hDA,hD,hcover⟩ := Finset.ruzsa_covering_add
    (Finset.image_nonempty.mpr hB) hsum'
  let q : ℝ → ℤ := fun x => ⌊x/δ⌋
  let g := Function.invFunOn q (A : Set ℝ)
  have hg (d : ℤ) (hd : d ∈ D) : g d ∈ A ∧ q (g d) = d :=
    Function.invFunOn_pos (Finset.mem_image.mp (hDA hd))
  let F := D.image g
  have hFA : F ⊆ A := by
    rintro f hf
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hf
    exact (hg d hd).1
  have hF : (F.card : ℝ) ≤ 2*K :=
    (Nat.cast_le.mpr (Finset.card_image_le (s := D) (f := g))).trans hD
  refine ⟨F,hFA,hF,?_⟩
  intro a ha
  have hqa : q a ∈ scalarCells δ A := Finset.mem_image.mpr ⟨a,ha,rfl⟩
  obtain ⟨d,hd,z,hz,he⟩ := Finset.mem_add.mp (hcover hqa)
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.mem_sub.mp hz
  obtain ⟨b,hb,hqb⟩ := Finset.mem_image.mp hu
  obtain ⟨c,hc,hqc⟩ := Finset.mem_image.mp hv
  refine ⟨g d,Finset.mem_image.mpr ⟨d,hd,rfl⟩,b,hb,c,hc,?_⟩
  have hqe : q a = q (g d)+q b-q c := by
    rw [(hg d hd).2]
    change q b = u at hqb
    change q c = v at hqc
    rw [hqb,hqc]
    omega
  have hqR : (q a : ℝ) = (q (g d) : ℝ)+(q b : ℝ)-(q c : ℝ) := by exact_mod_cast hqe
  have hqδ := congrArg (fun t : ℝ => t*δ) hqR
  have h0 (x : ℝ) : (q x : ℝ)*δ ≤ x := (le_div_iff₀ hδ).1 (Int.floor_le (x/δ))
  have h1 (x : ℝ) : x < ((q x : ℝ)+1)*δ := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x/δ))
  rw [abs_le]
  constructor <;> linarith [h0 a,h0 (g d),h0 b,h0 c,h1 a,h1 (g d),h1 b,h1 c]

end Falconer

end OAI
