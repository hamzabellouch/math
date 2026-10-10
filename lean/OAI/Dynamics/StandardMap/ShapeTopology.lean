import OAI.Dynamics.StandardMap.TreeLocalAffine

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology Classical
namespace StandardMapEntropy
def locallyAffineSet (d : ℝ → ℝ → ℝ) : Set ℝ := {x | ∃w,LocallyAffineAt d x w}
def locallyUnitSet (d : ℝ → ℝ → ℝ) : Set ℝ := {x | LocallyAffineAt d x 1}
lemma isOpen_locallyAffineSet (d : ℝ → ℝ → ℝ) : IsOpen (locallyAffineSet d) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨w,r,hr,hh⟩
  exact ⟨r,hr,fun y hy => ⟨w,locallyAffine_on_ball hh hy⟩⟩
lemma isOpen_locallyUnitSet (d : ℝ → ℝ → ℝ) : IsOpen (locallyUnitSet d) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨r,hr,hh⟩
  exact ⟨r,hr,fun y hy => locallyAffine_on_ball hh hy⟩
lemma affineOn_closure {d : ℝ → ℝ → ℝ} (hc : Continuous (Function.uncurry d))
    (U : Set ℝ) (w : ℝ) (ha : ∀x∈U,∀y∈U,d x y=w*|y-x|) :
    ∀x∈closure U,∀y∈closure U,d x y=w*|y-x| := by
  have h1 (x : ℝ) (hx : x∈U) : ∀y∈closure U,d x y=w*|y-x| := by
    apply closure_minimal (ha x hx)
    exact isClosed_eq (hc.comp (continuous_const.prodMk continuous_id))
      (continuous_const.mul ((continuous_id.sub continuous_const).abs))
  intro x hx y hy
  apply closure_minimal (fun z hz => h1 z hz y hy) _ hx
  exact isClosed_eq (hc.comp (continuous_id.prodMk continuous_const))
    (continuous_const.mul ((continuous_const.sub continuous_id).abs))
lemma affineOn_local {d : ℝ → ℝ → ℝ} (U : Set ℝ) (hU : IsOpen U) (w : ℝ)
    (ha : ∀x∈U,∀y∈U,d x y=w*|y-x|) (x : ℝ) (hx : x∈U) : LocallyAffineAt d x w := by
  obtain ⟨r,hr,hh⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨r,hr,fun y hy z hz => ha y (hh hy) z (hh hz)⟩
lemma closure_component_inter_open {F : Set ℝ} (hF : IsOpen F) {x z : ℝ} (hx : x∈F)
    (hz : z∈closure (connectedComponentIn F x)) (hzF : z∈F) : z∈connectedComponentIn F x := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hF z hzF
  obtain ⟨y,hy,hyz⟩ := Metric.mem_closure_iff.mp hz r hr
  have hyb : y∈ball z r := by simpa only [mem_ball,dist_comm] using hyz
  have hp : IsPreconnected (connectedComponentIn F x ∪ ball z r) :=
    IsPreconnected.union y hy hyb isPreconnected_connectedComponentIn (convex_ball z r).isPreconnected
  exact hp.subset_connectedComponentIn (Or.inl (mem_connectedComponentIn hx))
    (union_subset (connectedComponentIn_subset F x) hball) (Or.inr (mem_ball_self hr))
lemma frontier_component_not_mem {F : Set ℝ} (hF : IsOpen F) {x z : ℝ} (hx : x∈F)
    (hz : z∈frontier (connectedComponentIn F x)) : z∉F := by
  intro hzF
  have hm := closure_component_inter_open hF hx hz.1 hzF
  exact hz.2 (by simpa only [hF.connectedComponentIn.interior_eq] using hm)
lemma open_nonempty_inf_frontier {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hb : BddBelow U) : sInf U∈frontier U := by
  refine ⟨csInf_mem_closure hne hb,?_⟩
  rw [hU.interior_eq]
  intro hh
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU (sInf U) hh
  have hy : sInf U-r/2∈U := hball (by rw [mem_ball,Real.dist_eq]; rw [show sInf U-r/2-sInf U= -r/2 by ring,abs_div,abs_neg,abs_of_pos hr]; norm_num; linarith)
  have hi := csInf_le hb hy
  linarith
lemma open_nonempty_sup_frontier {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hb : BddAbove U) : sSup U∈frontier U := by
  refine ⟨csSup_mem_closure hne hb,?_⟩
  rw [hU.interior_eq]
  intro hh
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU (sSup U) hh
  have hy : sSup U+r/2∈U := hball (by rw [mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (by positivity)]; linarith)
  have hi := le_csSup hb hy
  linarith
lemma open_inf_lt_mem {U : Set ℝ} (hU : IsOpen U) (hb : BddBelow U) {x : ℝ} (hx : x∈U) : sInf U< x := by
  have hh := csInf_le hb hx
  apply lt_of_le_of_ne hh
  intro he
  have hf := open_nonempty_inf_frontier hU ⟨x,hx⟩ hb
  exact hf.2 (by simpa only [hU.interior_eq,he] using hx)
lemma open_mem_lt_sup {U : Set ℝ} (hU : IsOpen U) (hb : BddAbove U) {x : ℝ} (hx : x∈U) : x< sSup U := by
  have hh := le_csSup hb hx
  apply lt_of_le_of_ne hh
  intro he
  have hf := open_nonempty_sup_frontier hU ⟨x,hx⟩ hb
  exact hf.2 (by simpa only [hU.interior_eq,←he] using hx)
lemma ordConnected_eq_univ_of_unbounded {U : Set ℝ} (hU : OrdConnected U)
    (hlo : ¬BddBelow U) (hhi : ¬BddAbove U) : U=univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
  obtain ⟨z,hz,hxz⟩ := not_bddAbove_iff.mp hhi x
  exact hU.out hy hz ⟨hyx.le,hxz.le⟩
lemma open_ordConnected_eq_Ioi {U : Set ℝ} (hU : IsOpen U) (hC : OrdConnected U)
    (hne : U.Nonempty) (hlo : BddBelow U) (hhi : ¬BddAbove U) : U=Ioi (sInf U) := by
  ext x; constructor
  · exact open_inf_lt_mem hU hlo
  · intro hx
    obtain ⟨y,hy,hyx⟩ := (csInf_lt_iff hlo hne).mp hx
    obtain ⟨z,hz,hxz⟩ := not_bddAbove_iff.mp hhi x
    exact hC.out hy hz ⟨hyx.le,hxz.le⟩
lemma open_ordConnected_eq_Iio {U : Set ℝ} (hU : IsOpen U) (hC : OrdConnected U)
    (hne : U.Nonempty) (hlo : ¬BddBelow U) (hhi : BddAbove U) : U=Iio (sSup U) := by
  ext x; constructor
  · exact open_mem_lt_sup hU hhi
  · intro hx
    obtain ⟨y,hy,hyx⟩ := not_bddBelow_iff.mp hlo x
    obtain ⟨z,hz,hxz⟩ := (lt_csSup_iff hhi hne).mp hx
    exact hC.out hy hz ⟨hyx.le,hxz.le⟩
end StandardMapEntropy

end OAI
