import OAI.Analysis.AncientFlat.Evolution.InitialCore
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter Topology
namespace ParabolicShort
open ParabolicInterior ParabolicInitial
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [NormedAddCommGroup E]
lemma holder_initial_small (α α' h M : ℝ) (hα : 0<α) (haa : α<α')
    (hh : 0<h) (hh1 : h≤1) (hM : 0≤M) (g : V × ℝ → E)
    (h0 : ∀ x : V, ‖x‖<2 → g (x,0)=0)
    (hg : HolderBound α' (slab 2 h) g M) :
    HolderBound α (slab 1 h) g (2*h^((α'-α)/4)*M) := by
  let d := h^((1:ℝ)/4)
  have hd : 0<d := Real.rpow_pos_of_pos hh _
  have hd1 : d≤1 := Real.rpow_le_one hh.le hh1 (by norm_num)
  have hgap : 0<α'-α := sub_pos.mpr haa
  have hdgap : d^(α'-α)=h^((α'-α)/4) := by
    dsimp [d]; rw [←Real.rpow_mul hh.le]; congr 1; ring
  have hda : d^α'=d^(α'-α)*d^α := by rw [←Real.rpow_add hd]; congr 1; ring
  have hs (p : V × ℝ) (hp : p∈slab 1 h) : ‖g p‖≤M*d^α' := by
    have H := hg.2 p ⟨by linarith [hp.1],hp.2⟩ (p.1,0) ⟨by linarith [hp.1],le_rfl,hh.le⟩
    rw [h0 p.1 (by linarith [hp.1]),sub_zero] at H
    have he : pdist p (p.1,0)=p.2^((1:ℝ)/4) := by
      simp [pdist,abs_of_nonneg hp.2.1]
    rw [he] at H
    exact H.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Real.rpow_nonneg hp.2.1 _) (Real.rpow_le_rpow hp.2.1 hp.2.2 (by norm_num)) (hα.trans haa).le) hM)
  rw [←hdgap]
  constructor
  · intro p hp
    calc
      _≤M*d^α' := hs p hp
      _=M*d^(α'-α)*d^α := by rw [hda]; ring
      _≤M*d^(α'-α)*1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one hd.le hd1 hα.le) (by positivity)
      _≤_ := by nlinarith [Real.rpow_pos_of_pos hd (α'-α)]
  · intro p hp q hq
    let r := pdist p q
    have hr : 0≤r := by dsimp [r,pdist]; positivity
    have Hb : ‖g p-g q‖≤M*r^α' := hg.2 p ⟨by linarith [hp.1],hp.2⟩ q ⟨by linarith [hq.1],hq.2⟩
    change _≤2*d^(α'-α)*M*r^α
    by_cases hr0 : r=0
    · rw [hr0,Real.zero_rpow (hα.trans haa).ne',mul_zero] at Hb
      exact Hb.trans (by positivity)
    have hrp : 0<r := lt_of_le_of_ne hr (Ne.symm hr0)
    by_cases hrd : r≤d
    · have hra : r^α'=r^(α'-α)*r^α := by rw [←Real.rpow_add hrp]; congr 1; ring
      calc
        _≤M*r^α' := Hb
        _=M*r^(α'-α)*r^α := by rw [hra]; ring
        _≤M*d^(α'-α)*r^α := by gcongr
        _≤_ := by nlinarith [mul_nonneg (mul_nonneg hM (Real.rpow_nonneg hd.le (α'-α))) (Real.rpow_nonneg hr α)]
    · have Hsup : ‖g p-g q‖≤2*M*d^α' := (norm_sub_le _ _).trans (by linarith [hs p hp,hs q hq])
      calc
        _≤2*M*d^α' := Hsup
        _=2*d^(α'-α)*M*d^α := by rw [hda]; ring
        _≤_ := by gcongr; exact le_of_not_ge hrd

variable [InnerProductSpace ℝ V] [NormedSpace ℝ E]

lemma short_initial_jet_zero (u : V → E) (hu : ∀ x, ‖x‖<2 → u x=0) (j : ℕ)
    (x : V) (hx : ‖x‖<2) : iteratedFDeriv ℝ j u x=0 := by
  have he : u=ᶠ[𝓝 x] (fun _ => (0:E)) := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
    exact hu y hy
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  simp

theorem spatial_small (α α' : ℝ) (hα : 0<α) (haa : α<α') (_hα1 : α'<1) :
    ∃ C : ℝ, 0<C ∧ ∀ h M : ℝ, 0<h → h≤1 → 0≤M → ∀ (u : ℝ → V → E),
      (∀ x : V, ‖x‖<2 → u 0 x=0) →
      (∀ j : ℕ, j≤4 → HolderBound α' (slab 2 h)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) M) →
      ∀ j : ℕ, j≤4 → HolderBound α (slab 1 h)
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (C*h^((α'-α)/4)*M) := by
  refine ⟨2,by norm_num,?_⟩
  intro h M hh hh1 hM u hu0 hJ j hj
  exact holder_initial_small α α' h M hα haa hh hh1 hM _
    (fun x hx => short_initial_jet_zero (u 0) hu0 j x hx) (hJ j hj)
end ParabolicShort

end

end OAI
