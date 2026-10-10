import OAI.Geometry.NodalSets.Elliptic.RealTranslatedJetEmbedding

namespace OAI

namespace Yau.Geometry
open Yau.Analysis
open scoped ContDiff
noncomputable section

lemma real_coordinate_multilinear_norm (n : ℕ)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Yau.Jets.Coord) ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w : Fin n → Fin 4, ‖M (fun j ↦ Pi.single (w j) 1)‖ ≤ B) :
    ‖M‖ ≤ 4^n * B := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have he : v = fun j ↦ ∑ i : Fin 4, v j i • (Pi.single i 1 : Yau.Jets.Coord) := by
    ext j i
    simp [Pi.single_apply,Finset.sum_apply]
  calc
    ‖M v‖ = ‖∑ w : Fin n → Fin 4, M (fun j ↦ v j (w j) • Pi.single (w j) 1)‖ := by
      conv_lhs => rw [he,M.map_sum]
    _ ≤ ∑ w : Fin n → Fin 4, B * ∏ j, ‖v j‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro w _
      rw [M.map_smul_univ,norm_smul,Real.norm_eq_abs,Finset.abs_prod]
      have hp : (∏ j : Fin n, |v j (w j)|) ≤ ∏ j, ‖v j‖ :=
        Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (fun j _ ↦ norm_le_pi_norm (v j) (w j))
      exact (mul_le_mul hp (hb w) (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))).trans_eq
        (mul_comm _ _)
    _ = (4^n*B) * ∏ j, ‖v j‖ := by simp [mul_assoc]

lemma partialDirs_eq_get (ds : List (Fin 4)) :
    partialDirs ds = fun j ↦ (Pi.single (ds.get j) 1 : Yau.Jets.Coord) := by
  induction ds with
  | nil => ext j; exact Fin.elim0 j
  | cons i ds ih =>
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simpa only [partialDirs,Fin.cons_succ,Fin.val_succ,List.get_eq_getElem,List.getElem_cons_succ] using congrFun ih k

theorem iteratedFDeriv_norm_le_coordinate_bound (W : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (n : ℕ) (x : Yau.Jets.Coord) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ ds : List (Fin 4), ds.length=n → |partialJet W ds x| ≤ B) :
    ‖iteratedFDeriv ℝ n W x‖ ≤ 4^n * B := by
  apply real_coordinate_multilinear_norm n _ B hB
  intro w
  have he := partialJet_eq_iterated W hW (List.ofFn w) x
  simp only [partialDirs_eq_get,List.get_eq_getElem,List.getElem_ofFn] at he
  have he' : partialJet W (List.ofFn w) x =
      iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
    have aux (m : ℕ) (hm : m=n) :
        iteratedFDeriv ℝ m W x (fun j ↦ Pi.single (w (Fin.cast hm j)) 1) =
          iteratedFDeriv ℝ n W x (fun j ↦ Pi.single (w j) 1) := by
      subst m
      rfl
    exact he.trans (aux _ List.length_ofFn)
  rw [← he',Real.norm_eq_abs]
  exact hb _ List.length_ofFn

end
end Yau.Geometry

end OAI
