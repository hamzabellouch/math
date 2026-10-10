import OAI.Probability.ContinuumTransition.CubeBoundary

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem grand_local_moment_bound {κ : Type} [Fintype κ]
    (F : ConfigFamily) (Cset : κ → Set Space) (θ : κ → κ → ℝ)
    {D : Set Space} (hD : MeasurableSet D) (hDfin : volume D ≠ ⊤)
    (hCset : ∀ i, MeasurableSet (Cset i)) {c d v : ℝ}
    (hFrel : RelabelInvariant F)
    (hF0 : ∀ (ι : Type) [Fintype ι] (x : ι → Space), 0 ≤ F ι x)
    (hF : GrandFinite F D)
    (hfull : ∀ i, GrandFinite (momentFamily F (Cset i) c) D)
    (hhalf : ∀ i, GrandFinite (momentFamily F (Cset i) (c/2)) D)
    (hZ : 0 < grandIntegral F D)
    (hθ : ∀ i j, 0 ≤ θ i j) (hrow : ∀ i, ∑ j, θ i j ≤ 1)
    (hvol : ∀ i, volume.real (D ∩ Cset i) ≤ v)
    (hinsert : ∀ i (n : ℕ) (s : Finset (Fin n)) (x : Fin n → Space),
      x ∈ binaryRegion (D ∩ Cset i) (D \ Cset i) s →
        momentFamily F (Cset i) c (Fin n) x ≤ Real.exp (d*s.card)*
          (F {j : Fin n // j ∉ s} (fun j => x j)+
            ∑ k, θ i k*momentFamily F (Cset k) (c/2) {j : Fin n // j ∉ s} (fun j => x j))) :
    ∀ i, grandIntegral (momentFamily F (Cset i) c) D/grandIntegral F D ≤
      2*Real.exp (v*Real.exp d)+(Real.exp (v*Real.exp d))^2 := by
  let K := Real.exp (v*Real.exp d)
  have hK : 0 < K := Real.exp_pos _
  let G (i : κ) : ConfigFamily := fun ι _ x => F ι x+
    ∑ j, θ i j*momentFamily F (Cset j) (c/2) ι x
  have hG (i : κ) : GrandFinite (G i) D :=
    hF.add (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j)))
  have hG0 (i : κ) (ι : Type) [Fintype ι] (x : ι → Space) : 0 ≤ G i ι x :=
    add_nonneg (hF0 ι x) (Finset.sum_nonneg (fun j _ => mul_nonneg (hθ i j)
      (momentFamily_nonneg F hF0 _ _ ι x)))
  have hGrel (i : κ) : RelabelInvariant (G i) := by
    intro ι ν _ _ e x
    dsimp only [G]
    rw [hFrel ι ν e x]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [momentFamily_relabel F hFrel (Cset j) (c/2) ι ν e x]
  have hlin (i : κ) : grandIntegral (G i) D = grandIntegral F D+
      ∑ j, θ i j*grandIntegral (momentFamily F (Cset j) (c/2)) D := by
    rw [grandIntegral_add _ _ D (fun n => hF.integrable (Fin n))
      (fun n => (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j))).integrable (Fin n))
      hF.summable (GrandFinite.sum _ (fun j => (hhalf j).const_mul (θ i j))).summable]
    rw [grandIntegral_sum _ D (fun j n => ((hhalf j).const_mul (θ i j)).integrable (Fin n))
      (fun j => ((hhalf j).const_mul (θ i j)).summable)]
    simp_rw [grandIntegral_const_mul]
  have hamb (i : κ) : (D ∩ Cset i) ∪ (D \ Cset i) = D := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_sdiff]
    tauto
  have hb (i : κ) : grandIntegral (momentFamily F (Cset i) c) D ≤
      K*(grandIntegral F D+∑ j, θ i j*grandIntegral (momentFamily F (Cset j) (c/2)) D) := by
    have hBG := (hG i).mono_set (A := D \ Cset i) sdiff_subset (hG0 i)
    have hi := grandIntegral_insertion_bound (momentFamily F (Cset i) c) (G i) (hGrel i)
      (hD.inter (hCset i)) (hD.diff (hCset i))
      (by exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx.2))
      (ne_top_of_le_ne_top hDfin (measure_mono inter_subset_left))
      (fun n => by rw [hamb i]; exact (hfull i).integrable (Fin n))
      (fun ι _ => hBG.integrable ι)
      (by rw [hamb i]; exact (hfull i).summable) hBG.summable (hinsert i)
    rw [hamb i] at hi
    have hm := grandIntegral_mono_set (G i) sdiff_subset (hG0 i)
      (fun n => (hG i).integrable (Fin n)) hBG.summable (hG i).summable
    have he : Real.exp (volume.real (D ∩ Cset i)*Real.exp d) ≤ K :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hvol i) (Real.exp_pos _).le)
    exact hi.trans ((mul_le_mul he hm (grandIntegral_nonneg (G i) _ (hG0 i)) hK.le).trans_eq
      (by rw [hlin i]))
  apply finite_moment_bootstrap
    (fun i => grandIntegral (momentFamily F (Cset i) c) D/grandIntegral F D)
    (fun i => grandIntegral (momentFamily F (Cset i) (c/2)) D/grandIntegral F D)
    θ hK (fun i => div_nonneg (grandIntegral_nonneg _ _ (momentFamily_nonneg F hF0 _ _)) hZ.le)
    hθ hrow
  · intro i
    have hh := grandIntegral_half_moment_le F hD hK hF0 hF (hfull i) (hhalf i)
    apply (div_le_div_of_nonneg_right hh hZ.le).trans_eq
    field_simp
  · intro i
    apply (div_le_div_of_nonneg_right (hb i) hZ.le).trans_eq
    rw [mul_div_assoc, add_div, div_self hZ.ne', Finset.sum_div]
    simp_rw [mul_div_assoc]

end ContinuumTemperature
end

end OAI
