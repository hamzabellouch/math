import OAI.Probability.BenjaminiSchramm.SusceptibilityDerivativeLower

namespace OAI

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_susceptibility_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (p : unitInterval), p₀ ≤ (p : ℝ) → p < pc G →
      ∀ x b, c * susceptibility G p x ≤ susceptibility G p b ∧
        susceptibility G p b ≤ C * susceptibility G p x := by
  obtain ⟨O,hO⟩ := hqt
  have hqt : QuasiTransitive G := ⟨O,hO⟩
  let ι := {o : V // o ∈ O}
  let : Fintype ι := inferInstance
  obtain ⟨o,ho,_⟩ := hO (Classical.arbitrary V)
  let : Nonempty ι := ⟨⟨o,ho⟩⟩
  let root : ι → V := Subtype.val
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  let weight : ι → ℝ := fun _ => N⁻¹
  have hw (i : ι) : 0 ≤ weight i := inv_nonneg.mpr hN.le
  have hw1 : ∑ i, weight i = 1 := by
    simp only [weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact mul_inv_cancel₀ hN.ne'
  have hcover (x : V) : ∃ i, x ∈ vertexOrbit G (root i) := by
    obtain ⟨y,hy,a,b,hab,hax⟩ := hO x
    exact ⟨⟨y,hy⟩,a,b,hab,hax⟩
  obtain ⟨a,ha,hlo⟩ := exists_rootSusceptibility_lower G hconn hloc hqt root weight
    hw hw1 hcover p₀ hp₀
  have hupper (p : unitInterval) (x : V) :
      susceptibility G p x ≤ N * rootSusceptibility G root weight p :=
    susceptibility_le_rootSusceptibility G root weight hw hcover N hN.le
      (fun _ => by dsimp [weight]; rw [mul_inv_cancel₀ hN.ne']) p x
  let c := a/N
  have hc : 0 < c := div_pos ha hN
  have hcomp (p : unitInterval) (hp : p₀ ≤ (p : ℝ)) (hpp : p < pc G) (x b : V) :
      c * susceptibility G p x ≤ susceptibility G p b := by
    calc
      _ ≤ c * (N * rootSusceptibility G root weight p) :=
        mul_le_mul_of_nonneg_left (hupper p x) hc.le
      _ = a * rootSusceptibility G root weight p := by
        dsimp only [c]
        rw [←mul_assoc,div_mul_cancel₀ a hN.ne']
      _ ≤ _ := hlo p hp hpp b
  refine ⟨c,c⁻¹,hc,inv_pos.mpr hc,fun p hp hpp x b => ⟨hcomp p hp hpp x b,?_⟩⟩
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcomp p hp hpp b x)

end Percolation.BenjaminiSchramm

end OAI
