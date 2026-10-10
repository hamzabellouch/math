import OAI.MathematicalPhysics.Heisenberg.ExchangeOnMesh

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator NNReal
open Filter Topology
namespace Heisenberg.Surface
open ExchangeMatrix MeshPair
variable {V : Type} [Fintype V]

lemma color_matrix_permutation (π : Equiv.Perm V) :
    SlotColor.matrix π=permutationMatrix (SlotColor.permute π) := rfl

def colorClocks (a b : ℕ → V) : ℕ → List (Clock (V → Bool))
  | 0=>[]
  | n+1=>(⟨1/2,by norm_num⟩,SlotColor.permute (Equiv.swap (a n) (b n)))::colorClocks a b n

lemma color_prefix_linear (a b : ℕ → V) (q : ℕ) (δ : ℝ) :
    prefixMatrix (fun j=>colorCoin (a j) (b j) (δ/2)) q=linearMesh (colorClocks a b q) δ := by
  induction q with
  | zero=>rfl
  | succ q ih=>
    rw [prefixMatrix,ih,colorClocks,linearMesh]
    congr 1
    change (1-δ/2) • (1:Matrix (V → Bool) (V → Bool) ℝ)+(δ/2) •
      permutationMatrix (SlotColor.permute (Equiv.swap (a q) (b q)))=
      (1-(1/2:ℝ)*δ) • 1+((1/2:ℝ)*δ) • permutationMatrix (SlotColor.permute (Equiv.swap (a q) (b q)))
    rw [show δ/2=(1/2:ℝ)*δ by ring]

lemma color_generator (a b : ℕ → V) (q : ℕ) :
    clockGenerator (colorClocks a b q)=∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a j) (b j))-1) := by
  induction q with
  | zero=>simp [colorClocks,clockGenerator]
  | succ q ih=>
    rw [colorClocks,clockGenerator,ih,Finset.sum_range_succ]
    rw [color_matrix_permutation]
    exact add_comm _ _

theorem color_clock_limit (a b : ℕ → V) (q : ℕ) {t : ℝ} (ht : 0≤t) :
    Tendsto (fun n : ℕ=>(prefixMatrix (fun j=>colorCoin (a j) (b j) ((t/(n+1:ℝ))/2)) q)^(n+1)) atTop
      (𝓝 (NormedSpace.exp (t • ∑ j∈Finset.range q,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (a j) (b j))-1)))) := by
  simp_rw [color_prefix_linear]
  rw [←color_generator]
  exact linear_mesh_converges _ _ ht

end Heisenberg.Surface
end
end

end OAI
