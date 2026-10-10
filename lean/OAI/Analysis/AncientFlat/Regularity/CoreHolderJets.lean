import OAI.Analysis.AncientFlat.Regularity.CoreApplyHolder
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCore
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma norm_jet_fderiv_sub (j : ℕ) (f g : V → E) (x y : V) :
    ‖iteratedFDeriv ℝ j (fderiv ℝ f) x-iteratedFDeriv ℝ j (fderiv ℝ g) y‖=
      ‖iteratedFDeriv ℝ (j+1) f x-iteratedFDeriv ℝ (j+1) g y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  change ‖iteratedFDeriv ℝ j (fderiv ℝ f) x-iteratedFDeriv ℝ j (fderiv ℝ g) y‖=
    ‖(continuousMultilinearCurryRightEquiv' ℝ j V E).symm (iteratedFDeriv ℝ j (fderiv ℝ f) x)-
      (continuousMultilinearCurryRightEquiv' ℝ j V E).symm (iteratedFDeriv ℝ j (fderiv ℝ g) y)‖
  rw [←LinearIsometryEquiv.map_sub,LinearIsometryEquiv.norm_map]
lemma fderiv_jet_holder {α M : ℝ} {Ω : Set (V × ℝ)} (f : ℝ → V → E) (j : ℕ)
    (h : HolderBound α Ω (fun p => iteratedFDeriv ℝ (j+1) (f p.2) p.1) M) :
    HolderBound α Ω (fun p => iteratedFDeriv ℝ j (fderiv ℝ (f p.2)) p.1) M := by
  constructor
  · intro p hp
    rw [norm_iteratedFDeriv_fderiv]
    exact h.1 p hp
  · intro p hp q hq
    rw [norm_jet_fderiv_sub]
    exact h.2 p hp q hq
omit [InnerProductSpace ℝ V] in
lemma id_holder {α : ℝ} (hα : 0<α) (hα1 : α<1) {Ω : Set (V × ℝ)}
    (hx : ∀ p∈Ω, ‖p.1‖≤1) : HolderBound α Ω (fun p => p.1) 2 := by
  constructor
  · intro p hp; linarith [hx p hp]
  · intro p hp q hq
    have hd : ‖p.1-q.1‖≤pdist p q := by
      unfold pdist
      exact le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)
    have hz : 0≤pdist p q := pdist_nonneg p q
    by_cases hh : pdist p q≤1
    · have hr : pdist p q≤pdist p q^α := by
        conv_lhs => rw [←Real.rpow_one (pdist p q)]
        exact Real.rpow_le_rpow_of_exponent_ge' hz hh hα.le hα1.le
      have hn := Real.rpow_nonneg hz α
      linarith
    · have hr : 1≤pdist p q^α := Real.one_le_rpow (by linarith) hα.le
      have hb : ‖p.1-q.1‖≤2 := (norm_sub_le _ _).trans (by linarith [hx p hp,hx q hq])
      linarith
lemma positive_id_jet_constant (j : ℕ) (hj : j≠0) (x : V) :
    iteratedFDeriv ℝ j (id : V → V) x=iteratedFDeriv ℝ j (id : V → V) 0 := by
  have hc : ContDiff ℝ (j:ℕ∞ω) (id : V → V) := contDiff_id
  have ha := congrFun (iteratedFDeriv_add (f := id) (g := fun _ : V => x) hc contDiff_const) 0
  rw [Pi.add_apply,iteratedFDeriv_const_of_ne hj] at ha
  simp only [Pi.zero_apply,add_zero] at ha
  have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := (id : V → V)) j x (0:V)
  simpa only [Pi.add_apply,id_eq,zero_add] using ht.symm.trans ha
lemma id_jet_holder {α : ℝ} (hα : 0<α) (hα1 : α<1) {Ω : Set (V × ℝ)}
    (hx : ∀ p∈Ω, ‖p.1‖≤1) :
    ∀ j : ℕ, j≤2 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (id : V → V) p.1) 2 := by
  intro j hj
  constructor
  · intro p hp
    exact (id_jet_bound _ (hx p hp) j hj).trans (by norm_num)
  · intro p hp q hq
    by_cases hz : j=0
    · subst j
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←LinearIsometryEquiv.map_sub,
        LinearIsometryEquiv.norm_map,id_eq] using (id_holder hα hα1 hx).2 p hp q hq
    · change ‖iteratedFDeriv ℝ j (id : V → V) p.1-iteratedFDeriv ℝ j (id : V → V) q.1‖≤_
      rw [positive_id_jet_constant j hz p.1,positive_id_jet_constant j hz q.1,sub_self,norm_zero]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (pdist_nonneg p q) α)
end CompactCore

end

end OAI
