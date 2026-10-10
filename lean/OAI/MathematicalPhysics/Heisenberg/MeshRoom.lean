import OAI.MathematicalPhysics.Heisenberg.PeriodicCount

namespace OAI

section
noncomputable section
open scoped Classical
open Filter Topology
namespace Heisenberg.Surface
lemma mesh_room {s t δ : ℝ} (hs : 0 ≤ s) (hδ : 0<δ) (htδ : 2*(s+δ) ≤ t)
    (k Q : ℕ) (hk : δ*(k+1:ℝ)=t) :
    2*(⌊s/δ⌋₊+1)*Q≤(k+1)*Q := by
  apply Nat.mul_le_mul_right
  have hf:=Nat.floor_le (div_nonneg hs hδ.le)
  have hh:=mul_le_mul_of_nonneg_right hf hδ.le
  rw [div_mul_cancel₀ _ hδ.ne'] at hh
  have ht : (2:ℝ)*((⌊s/δ⌋₊:ℝ)+1)≤(k+1:ℝ) := by nlinarith
  exact_mod_cast ht

lemma mesh_step_tendsto (t : ℝ) : Tendsto (fun k : ℕ=>t/(k+1:ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma eventually_mesh_room {s t : ℝ} (hs : 0 ≤ s) (ht : 2*s < t) (Q : ℕ) :
    ∀ᶠ k : ℕ in atTop,2*(⌊s/(t/(k+1:ℝ))⌋₊+1)*Q≤(k+1)*Q := by
  have ht0 : 0<t:=by linarith
  have hh : ∀ᶠ k : ℕ in atTop,t/(k+1:ℝ)≤(t-2*s)/2 :=
    (mesh_step_tendsto t).eventually (eventually_le_nhds (by linarith))
  filter_upwards [hh] with k hk
  apply mesh_room (t := t) (δ := t/(k+1:ℝ)) hs (div_pos ht0 (by positivity)) (by linarith) k Q
  field_simp

end Heisenberg.Surface
end
end

end OAI
