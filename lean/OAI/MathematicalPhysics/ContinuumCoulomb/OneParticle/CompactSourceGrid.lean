import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CompactSourceTransport
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.InverseFifthCutoffGrid
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombTranslation

namespace OAI

/-! The fourth-order cell error for a compact orbital source, split into
cells near that source or the transport support and the remaining far cells. -/

noncomputable section
open MeasureTheory
open scoped Classical
namespace ContinuumCoulomb

def sourceExceptionalCell (E : Set Position) (u : PlanarPosition) (R : ℝ)
    (b : Position) (h : ℝ) : Prop :=
  (∃ x ∈ positionCube b h, x ∈ E) ∨ ‖planarCenter u-b‖ ≤ 4*R

theorem compact_source_grid_error :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : Position → ℝ), ContDiff ℝ 4 q → HasCompactSupport q →
      ∀ (B : ℝ), 0 ≤ B →
      (∀ k : ℕ, k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k q x‖ ≤ B) →
      (∀ k : ℕ, k ≤ 4 → (∫ x, ‖iteratedFDeriv ℝ k q x‖) ≤ B) →
      ∀ (u : PlanarPosition) (R : ℝ), 0 < R →
      (∀ x, q x ≠ 0 → ‖x-planarCenter u‖ ≤ R) →
      ∀ (G : Position → Position), ContDiff ℝ 4 G →
      ∀ (E : Set Position), (∀ x, x ∉ E → G x = x) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ x, ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ‖iteratedFDeriv ℝ k G x‖ ≤ D^k) →
      ∀ {ι : Type} [Fintype ι] (index : ι → Fin 3 → ℤ), Function.Injective index →
      ∀ (h : ℝ), 0 < h → h ≤ R →
      |(∑ i, positionCellGauss (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))-
        (∑ i, positionCellIntegral (gaussCellCenter h (index i)) h
          (fun x => NeutralAtom.potentialOf q (G x)))| ≤
        24*((2*Real.pi+1)*B)*D^4*h^4*
          ((Fintype.card {i // sourceExceptionalCell E u R (gaussCellCenter h (index i)) h}:ℕ):ℝ)*h^3+
        2048*Real.pi*C*B*h^4/R^2 := by
  obtain ⟨C,hC,hfar⟩ := compact_source_unchanged_cell_bound
  refine ⟨C,hC,?_⟩
  intro q hq hc B hB hb hi u R hR hsupp G hG E hfix D hD hGD ι _ index hindex h hh hhR
  let p : ι → Prop := fun i => sourceExceptionalCell E u R (gaussCellCenter h (index i)) h
  let Q : ι → ℝ := fun i => positionCellGauss (gaussCellCenter h (index i)) h
    (fun x => NeutralAtom.potentialOf q (G x))
  let I : ι → ℝ := fun i => positionCellIntegral (gaussCellCenter h (index i)) h
    (fun x => NeutralAtom.potentialOf q (G x))
  have hnear : |(∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val)| ≤
      24*((2*Real.pi+1)*B)*D^4*h^4*(Fintype.card {i // p i}:ℝ)*h^3 := by
    calc
      _ ≤ ∑ i : {i // p i}, |Q i.val-I i.val| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : {i // p i}, 24*((2*Real.pi+1)*B)*D^4*h^7 :=
        Finset.sum_le_sum (fun i _ => compact_source_transported_cell_bound hq hc hB hb hi
          G hG hD hGD _ hh.le)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  have hfi : Function.Injective (fun i : {i // ¬p i} => index i.val) :=
    fun i j hij => Subtype.ext (hindex hij)
  have hdist (i : {i // ¬p i}) : 4*R ≤ ‖planarCenter u-gaussCellCenter h (index i.val)‖ := by
    exact (lt_of_not_ge (fun he => i.property (Or.inr he))).le
  have hfs (i : {i // ¬p i}) :
      |Q i.val-I i.val| ≤
        (32*C*h^7/‖planarCenter u-gaussCellCenter h (index i.val)‖^5)*B := by
    let b := gaussCellCenter h (index i.val)
    have hd : 0 < ‖planarCenter u-b‖ := lt_of_lt_of_le (by positivity) (hdist i)
    have hf := hfar q hq hc G b h (‖planarCenter u-b‖/2) hh.le (by positivity)
      (fun x hx => hfix x (fun he => i.property (Or.inl ⟨x,hx,he⟩))) (fun x hx y hy => by
        have hs := hsupp x hx
        have hn := positionCube_norm_sub_le hh.le hy
        have ht := norm_sub_le_norm_sub_add_norm_sub (planarCenter u) x b
        have ht' := norm_sub_le_norm_sub_add_norm_sub x y b
        rw [norm_sub_rev (planarCenter u) x] at ht
        rw [norm_sub_rev x y] at ht'
        have := hdist i
        change 4*R ≤ ‖planarCenter u-b‖ at this
        linarith)
    have hm : (∫ x, ‖q x‖) ≤ B := by simpa only [norm_iteratedFDeriv_zero] using hi 0 (by omega)
    apply hf.trans
    have hfac : 0 ≤ C*h^7/(‖planarCenter u-b‖/2)^5 := by positivity
    apply (mul_le_mul_of_nonneg_left hm hfac).trans_eq
    change C*h^7/(‖planarCenter u-b‖/2)^5*B = (32*C*h^7/‖planarCenter u-b‖^5)*B
    field_simp
    ring
  have hfarSum : |(∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)| ≤
      2048*Real.pi*C*B*h^4/R^2 := by
    calc
      _ ≤ ∑ i : {i // ¬p i}, |Q i.val-I i.val| := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : {i // ¬p i}, (32*C*h^7/‖planarCenter u-gaussCellCenter h (index i.val)‖^5)*B :=
        Finset.sum_le_sum (fun i _ => hfs i)
      _ = (32*C*B*h^4)*(∑ i : {i // ¬p i}, h^3/‖planarCenter u-gaussCellCenter h (index i.val)‖^5) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ (32*C*B*h^4)*(64*Real.pi/R^2) :=
        mul_le_mul_of_nonneg_left (inverseFifth_cutoff_grid_sum _ hfi hh hR hhR _ hdist) (by positivity)
      _ = _ := by ring
  have heQ := Fintype.sum_subtype_add_sum_subtype p Q
  have heI := Fintype.sum_subtype_add_sum_subtype p I
  change |(∑ i, Q i)-(∑ i, I i)| ≤ _
  rw [← heQ,← heI]
  have ht := abs_add_le ((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))
    ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val))
  have he : ((∑ i : {i // p i}, Q i.val)+(∑ i : {i // ¬p i}, Q i.val))-
      ((∑ i : {i // p i}, I i.val)+(∑ i : {i // ¬p i}, I i.val)) =
      ((∑ i : {i // p i}, Q i.val)-(∑ i : {i // p i}, I i.val))+
      ((∑ i : {i // ¬p i}, Q i.val)-(∑ i : {i // ¬p i}, I i.val)) := by ring
  rw [he]
  exact ht.trans (add_le_add hnear hfarSum)

end ContinuumCoulomb

end

end OAI
