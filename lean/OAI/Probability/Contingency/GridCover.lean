import Mathlib
import OAI.Probability.Contingency.DenseAnalytic

namespace OAI

/-! Grid Cover. -/

noncomputable section

open Set MeasureTheory
open Set MeasureTheory
open scoped Pointwise
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
open Contingency.Interpolation

theorem neighbors_symm (v w : Fin q → ℕ) (i : Fin q) (hn : neighbors v w i) : neighbors w v i :=
  ⟨hn.1.symm,fun j hj => (hn.2 j hj).symm⟩

theorem neighbors_unique (v w : Fin q → ℕ) (i j : Fin q)
    (hi : neighbors v w i) (hj : neighbors v w j) : i=j := by
  by_contra hne
  have he := hj.2 i hne
  rcases hi.1 with h | h <;> omega

theorem faceBox_swap (v w : Vertex q K) (i : Fin q) (r : ℝ)
    (hn : neighbors (corner v) (corner w) i) : faceBox v w i r=faceBox w v i r := by
  unfold faceBox
  congr 1 <;> funext j <;> split_ifs with hj
  · rw [max_comm]
  · have hh := hn.2 j hj
    dsimp [corner] at hh
    rw [hh]
  · rw [max_comm]
  · have hh := hn.2 j hj
    dsimp [corner] at hh
    rw [hh]

def Cut (V : Finset (Vertex q K)) :=
  {e : Vertex q K×Vertex q K // e.1∈V ∧ e.2∉V ∧ ∃ i,neighbors (corner e.1) (corner e.2) i}

instance cutFintype (V : Finset (Vertex q K)) : Fintype (Cut V) := by unfold Cut; exact Fintype.ofFinite _

def Cut.coord {V : Finset (Vertex q K)} (e : Cut V) : Fin q := Classical.choose e.property.2.2

theorem Cut.adjacent {V : Finset (Vertex q K)} (e : Cut V) :
    neighbors (corner e.val.1) (corner e.val.2) e.coord := Classical.choose_spec e.property.2.2

def Cut.neighborhood {V : Finset (Vertex q K)} (e : Cut V) (r : ℝ) : OpenBox q := faceBox e.val.1 e.val.2 e.coord r

theorem cut_cover_endpoints (V : Finset (Vertex q K)) (v w : Vertex q K) (hv : v∈V) (hw : w∉V)
    (x z : Fin q → ℝ) (hx : inside (corner v) x) (hz : inside (corner w) z)
    (r : ℝ) (hr : r ≤ 1) (hc : ∀ i,|x i-z i|<r) :
    ∃ e : Cut V,z∈(e.neighborhood r).carrier := by
  obtain ⟨u,u',i,hn,hl,hz⟩ := bounded_cut_face V v w hv hw x z hx hz r hr hc
  rcases hl with ⟨hu,hu'⟩ | ⟨hu,hu'⟩
  · let e : Cut V := ⟨(u,u'),hu,hu',i,hn⟩
    have he : e.coord=i := neighbors_unique _ _ _ _ e.adjacent hn
    exact ⟨e,by simpa only [Cut.neighborhood,he] using hz⟩
  · let e : Cut V := ⟨(u',u),hu',hu,i,neighbors_symm _ _ _ hn⟩
    have he : e.coord=i := neighbors_unique _ _ _ _ e.adjacent (neighbors_symm _ _ _ hn)
    refine ⟨e,?_⟩
    change z∈(faceBox u' u e.coord r).carrier
    rw [he,← faceBox_swap u u' i r hn]
    exact hz

 

theorem minkowski_cut_cover (V : Finset (Vertex q K)) (t : ℝ)
    (ht : 0<t) (ht1 : t<1) (hr : t*(K:ℝ) ≤ 1) :
    ∀ᵐ z : Fin q → ℝ ∂volume,
      z∈boxUnion (mixBoxes (boxes V) {cube q K} (1-t) t) \ boxUnion (boxes V) →
      ∃ e : Cut V,z∈(e.neighborhood (t*K)).carrier := by
  filter_upwards [ae_no_grid (q:=q)] with z hgrid
  rintro ⟨hz,hnz⟩
  obtain ⟨x,hx,y,hy,he⟩ := (mem_mixBoxes (boxes V) {cube q K} (1-t) t (by linarith) ht z).mp hz
  have hy' : ∀ i,0<y i ∧ y i<(K:ℝ) := (mem_cube y).mp (by simpa [boxUnion] using hy)
  have hx' := (mem_cube x).mp (bins_subset_cube V hx)
  have he' (i : Fin q) : z i=(1-t)*x i+t*y i := by simpa using (congrFun he i).symm
  have hzcube : z∈(cube q K).carrier := by
    apply (mem_cube z).mpr
    intro i
    rw [he']
    constructor
    · exact add_pos (mul_pos (by linarith) (hx' i).1) (mul_pos ht (hy' i).1)
    · have h1 := mul_lt_mul_of_pos_left (hx' i).2 (show 0<1-t by linarith)
      have h2 := mul_lt_mul_of_pos_left (hy' i).2 ht
      nlinarith only [h1,h2]
  obtain ⟨v,hv,hvx⟩ := (mem_boxes V x).mp hx
  obtain ⟨w,hwz⟩ := exists_bin z hzcube hgrid
  have hw : w∉V := fun hh => hnz ((mem_boxes V z).mpr ⟨w,hh,hwz⟩)
  apply cut_cover_endpoints V v w hv hw x z hvx hwz (t*K) hr
  intro i
  have hd : |x i-y i|<(K:ℝ) := by rw [abs_lt]; constructor <;> linarith [(hx' i).1,(hx' i).2,(hy' i).1,(hy' i).2]
  rw [he']
  have heq : x i-((1-t)*x i+t*y i)=t*(x i-y i) := by ring
  rw [heq,abs_mul,abs_of_pos ht]
  exact mul_lt_mul_of_pos_left hd ht

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
open Contingency.Interpolation

theorem box_integrable (F : GoodWeight q) (B : OpenBox q) : IntegrableOn F.f B.carrier := by
  simpa only [boxUnion,Finset.mem_singleton,iUnion_iUnion_eq_left] using F.integrable {B}

theorem bin_volume (v : Vertex q K) : volume (bin v).carrier=1 := by
  simp [bin,OpenBox.carrier,volume_pi_pi]

theorem box_volume_real (B : OpenBox q) (hp : ∀ i,B.lower i ≤ B.upper i) :
    (volume B.carrier).toReal=∏ i,(B.upper i-B.lower i) := by
  simp only [OpenBox.carrier,volume_pi_pi,Real.volume_Ioo,ENNReal.toReal_prod]
  congr 1
  funext i
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hp i))

theorem faceBox_volume (v w : Vertex q K) (i : Fin q) (r : ℝ) (hr : 0 ≤ r) :
    (volume (faceBox v w i r).carrier).toReal=2*r*(1+2*r)^(q-1) := by
  have hlen (j : Fin q) : (faceBox v w i r).upper j-(faceBox v w i r).lower j=
      if j=i then 2*r else 1+2*r := by
    dsimp [faceBox]
    split_ifs <;> ring
  rw [box_volume_real _ (fun j => sub_nonneg.mp (by rw [hlen]; split_ifs <;> positivity))]
  simp_rw [hlen]
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => if j=i then 2*r else 1+2*r) (Finset.mem_univ i)]
  simp only [ite_true]
  have he : (∏ j∈Finset.univ.erase i,if j=i then 2*r else 1+2*r)=(1+2*r)^(q-1) := by
    calc
      _ = ∏ _j∈Finset.univ.erase i,(1+2*r) := Finset.prod_congr rfl (fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj))
      _ = _ := by simp
  rw [he]

theorem integral_boxes (F : GoodWeight q) (V : Finset (Vertex q K)) :
    (∫ x in boxUnion (boxes V),F.f x)=∑ v∈V,∫ x in (bin v).carrier,F.f x := by
  have hs : boxUnion (boxes V)=⋃ v∈V,(bin v).carrier := by
    ext x
    simp only [mem_boxes,Set.mem_iUnion,mem_bin]
    constructor <;> rintro ⟨v,hv,hx⟩ <;> exact ⟨v,hv,hx⟩
  rw [hs]
  apply integral_biUnion_finset V
  · intro v _; exact (bin v).isOpen.measurableSet
  · intro v _ w _ hne; exact bins_disjoint hne
  · intro v _; exact box_integrable F (bin v)

theorem bin_integral_bounds (F : GoodWeight q) (W : Vertex q K → ℝ)
    (hp : ∀ v x,x∈(bin v).carrier → W v/4 ≤ F.f x ∧ F.f x ≤ 4*W v) (v : Vertex q K) :
    W v/4 ≤ ∫ x in (bin v).carrier,F.f x ∧ (∫ x in (bin v).carrier,F.f x) ≤ 4*W v := by
  have hi := box_integrable F (bin v)
  have hj (a : ℝ) : IntegrableOn (fun _ : Fin q → ℝ => a) (bin v).carrier :=
    integrableOn_const (by rw [bin_volume]; exact ENNReal.one_ne_top)
  have hc (a : ℝ) : (∫ _ in (bin v).carrier,a)=a := by simp [bin_volume,Measure.real]
  constructor
  · rw [← hc (W v/4)]
    exact setIntegral_mono_on (hj _) hi (bin v).isOpen.measurableSet (fun x hx => (hp v x hx).1)
  · rw [← hc (4*W v)]
    exact setIntegral_mono_on hi (hj _) (bin v).isOpen.measurableSet (fun x hx => (hp v x hx).2)

theorem boxes_integral_bounds (F : GoodWeight q) (W : Vertex q K → ℝ)
    (hp : ∀ v x,x∈(bin v).carrier → W v/4 ≤ F.f x ∧ F.f x ≤ 4*W v) (V : Finset (Vertex q K)) :
    (∑ v∈V,W v)/4 ≤ ∫ x in boxUnion (boxes V),F.f x ∧
      (∫ x in boxUnion (boxes V),F.f x) ≤ 4*∑ v∈V,W v := by
  rw [integral_boxes]
  constructor
  · rw [Finset.sum_div]
    exact Finset.sum_le_sum fun v _ => (bin_integral_bounds F W hp v).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => (bin_integral_bounds F W hp v).2

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators Pointwise
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
open Contingency.Interpolation

theorem face_volume_bound (d : ℝ) (hd : 1 ≤ d) (hq : (q:ℝ) ≤ d)
    (v w : Vertex q K) (i : Fin q) :
    (volume (faceBox v w i (1/(4*d))).carrier).toReal ≤ 1 := by
  have hd0 : 0<d := by linarith
  rw [faceBox_volume _ _ _ _ (by positivity)]
  have hexp : (1+2*(1/(4*d)))^(q-1) ≤ 2 := by
    calc
      _ ≤ (Real.exp (2*(1/(4*d))))^(q-1) := by
        apply pow_le_pow_left₀ (by positivity)
        linarith only [Real.add_one_le_exp (2*(1/(4*d)))]
      _ = Real.exp ((q-1:ℕ)*(2*(1/(4*d)))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (1/2) := by
        apply Real.exp_le_exp.mpr
        have hq' : ((q-1:ℕ):ℝ) ≤ d := (Nat.cast_le.mpr (Nat.sub_le q 1)).trans hq
        have he : ((q-1:ℕ):ℝ)*(2*(1/(4*d)))=((q-1:ℕ):ℝ)/(2*d) := by ring
        rw [he]
        apply (div_le_iff₀ (by positivity : 0<2*d)).mpr
        linarith only [hq']
      _ ≤ 2 := by have hh := Real.exp_bound_div_one_sub_of_interval (x:=1/2) (by norm_num) (by norm_num); norm_num at hh ⊢; exact hh
  have hmul := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2*(1/(4*d)) by positivity)
  calc
    _ ≤ 2*(1/(4*d))*2 := hmul
    _ = 1/d := by ring
    _ ≤ 1 := (div_le_one hd0).mpr hd

theorem integral_cover (F : GoodWeight q) (V : Finset (Vertex q K)) (t : ℝ)
    (ht : 0<t) (ht1 : t<1) (hr : t*(K:ℝ) ≤ 1) :
    (∫ z in boxUnion (mixBoxes (boxes V) {cube q K} (1-t) t) \ boxUnion (boxes V),F.f z) ≤
      ∑ e : Cut V,∫ z in (e.neighborhood (t*K)).carrier,F.f z := by
  classical
  let G := boxUnion (mixBoxes (boxes V) {cube q K} (1-t) t) \ boxUnion (boxes V)
  have hG : MeasurableSet G := (boxUnion_measurable _).diff (boxUnion_measurable _)
  have hiG : Integrable (G.indicator F.f) :=
    ((F.integrable _).mono_set sdiff_subset).integrable_indicator hG
  have hi (e : Cut V) : Integrable ((e.neighborhood (t*K)).carrier.indicator F.f) :=
    (box_integrable F _).integrable_indicator (e.neighborhood (t*K)).isOpen.measurableSet
  have hh : (∫ z,G.indicator F.f z) ≤ ∫ z,∑ e : Cut V,(e.neighborhood (t*K)).carrier.indicator F.f z := by
    apply integral_mono_ae hiG (integrable_finsetSum _ (fun e _ => hi e))
    filter_upwards [minkowski_cut_cover V t ht ht1 hr] with z hz
    have hnon (e : Cut V) : 0 ≤ (e.neighborhood (t*K)).carrier.indicator F.f z := by
      by_cases he : z∈(e.neighborhood (t*K)).carrier <;> simp [he,(F.positive z).le]
    by_cases hzG : z∈G
    · obtain ⟨e,he⟩ := hz hzG
      rw [Set.indicator_of_mem hzG]
      calc
        _ = (e.neighborhood (t*K)).carrier.indicator F.f z := (Set.indicator_of_mem he _).symm
        _ ≤ _ := Finset.single_le_sum (fun e _ => hnon e) (Finset.mem_univ e)
    · rw [Set.indicator_of_notMem hzG]
      exact Finset.sum_nonneg fun e _ => hnon e
  rw [integral_indicator hG,integral_finsetSum _ (fun e _ => hi e)] at hh
  simp_rw [integral_indicator ((Cut.neighborhood _ _).isOpen.measurableSet)] at hh
  exact hh

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators Pointwise
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
open Contingency.Interpolation

def border (V : Finset (Vertex q K)) (W : Vertex q K → ℝ) : ℝ :=
  ∑ e : Cut V,min (W e.val.1) (W e.val.2)

def Cut.reverse (V : Finset (Vertex q K)) : Cut V ≃ Cut Vᶜ where
  toFun e := ⟨(e.val.2,e.val.1),by
    refine ⟨by simpa using e.property.2.1,by simpa using e.property.1,?_⟩
    exact ⟨e.coord,neighbors_symm _ _ _ e.adjacent⟩⟩
  invFun e := ⟨(e.val.2,e.val.1),by
    refine ⟨by simpa using e.property.2.1,by simpa using e.property.1,?_⟩
    exact ⟨e.coord,neighbors_symm _ _ _ e.adjacent⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem border_compl (V : Finset (Vertex q K)) (W : Vertex q K → ℝ) :
    border Vᶜ W=border V W := by
  unfold border
  rw [← (Cut.reverse V).sum_comp (fun e => min (W e.val.1) (W e.val.2))]
  apply Finset.sum_congr rfl
  intro e _
  exact min_comm _ _

theorem mass_partition (F : GoodWeight q) (V : Finset (Vertex q K)) :
    (∫ x in boxUnion (boxes V),F.f x)+(∫ x in boxUnion (boxes Vᶜ),F.f x)=
      ∫ x in (cube q K).carrier,F.f x := by
  rw [integral_boxes,integral_boxes,Finset.sum_add_sum_compl]
  rw [← integral_boxes F Finset.univ]
  exact setIntegral_congr_set cube_ae_union

theorem boxes_nonempty (V : Finset (Vertex q K)) (hV : V.Nonempty) :
    (boxUnion (boxes V)).Nonempty := by
  obtain ⟨v,hv⟩ := hV
  refine ⟨fun i => (v i:ℝ)+1/2,(mem_boxes V _).mpr ⟨v,hv,?_⟩⟩
  intro i
  dsimp [corner]
  constructor <;> linarith

theorem face_integral_bound (F : GoodWeight q) (W : Vertex q K → ℝ)
    (hW : ∀ v,0 ≤ W v) (d : ℝ) (hd : 1 ≤ d) (hq : (q:ℝ) ≤ d)
    (hp : ∀ (v w : Vertex q K) (i : Fin q),neighbors (corner v) (corner w) i →
      ∀ x,x∈(faceBox v w i (1/(4*d))).carrier → F.f x ≤ 4*min (W v) (W w))
    (V : Finset (Vertex q K)) (e : Cut V) :
    (∫ x in (e.neighborhood (1/(4*d))).carrier,F.f x) ≤ 4*min (W e.val.1) (W e.val.2) := by
  let B := e.neighborhood (1/(4*d))
  calc
    _ ≤ ∫ _x in B.carrier,4*min (W e.val.1) (W e.val.2) :=
      setIntegral_mono_on (box_integrable F B) (integrableOn_const B.isBounded.measure_lt_top.ne) B.isOpen.measurableSet
        (hp _ _ _ e.adjacent)
    _ = (volume B.carrier).toReal*(4*min (W e.val.1) (W e.val.2)) := by simp [Measure.real]
    _ ≤ _ := by
      exact mul_le_of_le_one_left (mul_nonneg (by norm_num) (le_min (hW _) (hW _))) (face_volume_bound d hd hq _ _ _)

theorem small_side_border (F : GoodWeight q) (W : Vertex q K → ℝ)
    (hW : ∀ v,0 ≤ W v) (d : ℝ) (hd : 1 ≤ d) (hq : (q:ℝ) ≤ d) (hK : 1 ≤ K)
    (hc : ∀ x y (α β : ℝ),0 ≤ α → 0 ≤ β → α+β=1 → F.f x^α*F.f y^β ≤ F.f (α • x+β • y))
    (hb : ∀ v x,x∈(bin v).carrier → W v/4 ≤ F.f x ∧ F.f x ≤ 4*W v)
    (hp : ∀ (v w : Vertex q K) (i : Fin q),neighbors (corner v) (corner w) i →
      ∀ x,x∈(faceBox v w i (1/(4*d))).carrier → F.f x ≤ 4*min (W v) (W w))
    (V : Finset (Vertex q K)) (hV : V.Nonempty)
    (hsmall : 2*(∫ x in boxUnion (boxes V),F.f x) ≤ ∫ x in (cube q K).carrier,F.f x) :
    Real.log 2/(64*d*K)*(∑ v∈V,W v) ≤ border V W := by
  let t : ℝ := 1/(4*d*K)
  have hd0 : 0<d := by linarith
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (0:ℝ)<K := by linarith
  have ht : 0<t := by dsimp [t]; positivity
  have ht1 : t<1 := by dsimp [t]; apply (div_lt_one (by positivity)).mpr; nlinarith
  have hr : t*(K:ℝ)=1/(4*d) := by dsimp [t]; field_simp
  have hr1 : t*(K:ℝ) ≤ 1 := by rw [hr]; apply (div_le_one (by positivity)).mpr; linarith
  have hsub : boxUnion (boxes V) ⊆ boxUnion ({cube q K} : Finset (OpenBox q)) := by
    simpa only [boxUnion,Finset.mem_singleton,iUnion_iUnion_eq_left] using bins_subset_cube V
  have hgain := mass_gain (boxes V) {cube q K} F hsub (boxes_nonempty V hV)
    (by simpa only [boxUnion,Finset.mem_singleton,iUnion_iUnion_eq_left] using hsmall) t ht ht1
    (fun x y => hc x y (1-t) t (by linarith) ht.le (by ring))
  have hcover := integral_cover F V t ht ht1 hr1
  rw [hr] at hcover
  have hface : (∑ e : Cut V,∫ x in (e.neighborhood (1/(4*d))).carrier,F.f x) ≤ 4*border V W := by
    unfold border
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => face_integral_bound F W hW d hd hq hp V e
  have hlower := (boxes_integral_bounds F W hb V).1
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmult := mul_le_mul_of_nonneg_left hlower (mul_nonneg ht.le hlog.le)
  have he : t*Real.log 2*((∑ v∈V,W v)/4)/4=Real.log 2/(64*d*K)*(∑ v∈V,W v) := by dsimp [t]; ring
  rw [← he]
  linarith only [hmult,hgain,hcover,hface]

 

theorem border_bound (F : GoodWeight q) (W : Vertex q K → ℝ)
    (hW : ∀ v,0 ≤ W v) (d : ℝ) (hd : 1 ≤ d) (hq : (q:ℝ) ≤ d) (hK : 1 ≤ K)
    (hc : ∀ x y (α β : ℝ),0 ≤ α → 0 ≤ β → α+β=1 → F.f x^α*F.f y^β ≤ F.f (α • x+β • y))
    (hb : ∀ v x,x∈(bin v).carrier → W v/4 ≤ F.f x ∧ F.f x ≤ 4*W v)
    (hp : ∀ (v w : Vertex q K) (i : Fin q),neighbors (corner v) (corner w) i →
      ∀ x,x∈(faceBox v w i (1/(4*d))).carrier → F.f x ≤ 4*min (W v) (W w))
    (V : Finset (Vertex q K)) (hV : V.Nonempty) (hVc : Vᶜ.Nonempty) :
    Real.log 2/(64*d*K)*min (∑ v∈V,W v) (∑ v∈Vᶜ,W v) ≤ border V W := by
  have hnon : 0 ≤ Real.log 2/(64*d*K) := by positivity
  have hm := mass_partition F V
  by_cases hs : 2*(∫ x in boxUnion (boxes V),F.f x) ≤ ∫ x in (cube q K).carrier,F.f x
  · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hnon).trans
      (small_side_border F W hW d hd hq hK hc hb hp V hV hs)
  · have hs' : 2*(∫ x in boxUnion (boxes Vᶜ),F.f x) ≤ ∫ x in (cube q K).carrier,F.f x := by linarith
    have hh := small_side_border F W hW d hd hq hK hc hb hp Vᶜ hVc hs'
    rw [border_compl] at hh
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hnon).trans hh

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators Pointwise
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}

 
def realCorner (v : Vertex q K) : Fin q → ℝ := fun i => v i

 
def exponentWeight (g : (Fin q → ℝ) → ℝ) (v : Vertex q K) : ℝ :=
  (2:ℝ)^(-(⌊g (realCorner v)⌋:ℝ))

theorem exponentWeight_pos (g : (Fin q → ℝ) → ℝ) (v : Vertex q K) :
    0<exponentWeight g v := Real.rpow_pos_of_pos (by norm_num) _

theorem exponentWeight_upper (g : (Fin q → ℝ) → ℝ) (v : Vertex q K) (x : Fin q → ℝ)
    (hh : g (realCorner v)-g x ≤ 2) : (2:ℝ)^(-g x) ≤ 4*exponentWeight g v := by
  have hf := Int.floor_le (g (realCorner v))
  calc
    _ ≤ (2:ℝ)^(-(⌊g (realCorner v)⌋:ℝ)+2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]; norm_num [exponentWeight]; ring

theorem exponentWeight_lower (g : (Fin q → ℝ) → ℝ) (v : Vertex q K) (x : Fin q → ℝ)
    (hh : g x-g (realCorner v) ≤ 1) : exponentWeight g v/4 ≤ (2:ℝ)^(-g x) := by
  have hf := Int.lt_floor_add_one (g (realCorner v))
  calc
    _ = (2:ℝ)^(-(⌊g (realCorner v)⌋:ℝ)-2) := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]; norm_num [exponentWeight]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem bin_distance (v : Vertex q K) (x : Fin q → ℝ) (hx : x∈(bin v).carrier) :
    ‖x-realCorner v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  have hh := (mem_bin v x).mp hx i
  dsimp [inside,corner] at hh
  simp only [Pi.sub_apply,realCorner,Real.norm_eq_abs,abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem face_distance (v w : Vertex q K) (i : Fin q) (r : ℝ) (hr : 0 ≤ r)
    (hn : neighbors (corner v) (corner w) i) (x : Fin q → ℝ)
    (hx : x∈(faceBox v w i r).carrier) : ‖x-realCorner v‖ ≤ 1+r := by
  apply (pi_norm_le_iff_of_nonneg (by linarith : (0:ℝ) ≤ 1+r)).mpr
  intro j
  have hh := (Set.mem_pi.mp hx) j (Set.mem_univ j)
  simp only [Set.mem_Ioo,faceBox] at hh
  simp only [Pi.sub_apply,realCorner,Real.norm_eq_abs,abs_le]
  by_cases hj : j=i
  · subst j
    simp only [ite_true,Nat.cast_max] at hh
    have hn' := hn.1
    dsimp [corner] at hn'
    rcases hn' with h | h
    · have he : (v i:ℝ)+1=(w i:ℝ) := by exact_mod_cast h
      have hm : max (v i:ℝ) (w i:ℝ)=(w i:ℝ) := max_eq_right (by linarith)
      rw [hm] at hh
      constructor <;> linarith [hh.1,hh.2]
    · have he : (w i:ℝ)+1=(v i:ℝ) := by exact_mod_cast h
      have hm : max (v i:ℝ) (w i:ℝ)=(v i:ℝ) := max_eq_left (by linarith)
      rw [hm] at hh
      constructor <;> linarith [hh.1,hh.2]
  · simp only [hj,ite_false] at hh
    constructor <;> linarith [hh.1,hh.2]

theorem weight_bin_comparison (g : (Fin q → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L) (hL1 : L ≤ 1)
    (hg : ∀ x y,|g x-g y| ≤ L*‖x-y‖)
    (v : Vertex q K) (x : Fin q → ℝ) (hx : x∈(bin v).carrier) :
    exponentWeight g v/4 ≤ (2:ℝ)^(-g x) ∧ (2:ℝ)^(-g x) ≤ 4*exponentWeight g v := by
  have hh : |g x-g (realCorner v)| ≤ 1 :=
    (hg x (realCorner v)).trans ((mul_le_mul_of_nonneg_left (bin_distance v x hx) hL).trans (by simpa using hL1))
  constructor
  · exact exponentWeight_lower g v x (abs_le.mp hh).2
  · apply exponentWeight_upper
    linarith only [(abs_le.mp hh).1]

theorem weight_face_comparison (g : (Fin q → ℝ) → ℝ) (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hLr : L*(1+r) ≤ 2) (hg : ∀ x y,|g x-g y| ≤ L*‖x-y‖)
    (v w : Vertex q K) (i : Fin q) (hn : neighbors (corner v) (corner w) i)
    (x : Fin q → ℝ) (hx : x∈(faceBox v w i r).carrier) :
    (2:ℝ)^(-g x) ≤ 4*min (exponentWeight g v) (exponentWeight g w) := by
  have hv : (2:ℝ)^(-g x) ≤ 4*exponentWeight g v := by
    apply exponentWeight_upper
    have hh := (hg x (realCorner v)).trans ((mul_le_mul_of_nonneg_left (face_distance v w i r hr hn x hx) hL).trans hLr)
    linarith only [(abs_le.mp hh).1]
  have hw : (2:ℝ)^(-g x) ≤ 4*exponentWeight g w := by
    apply exponentWeight_upper
    have hx' : x∈(faceBox w v i r).carrier := by rw [← faceBox_swap v w i r hn]; exact hx
    have hh := (hg x (realCorner w)).trans ((mul_le_mul_of_nonneg_left (face_distance w v i r hr (neighbors_symm _ _ _ hn) x hx') hL).trans hLr)
    linarith only [(abs_le.mp hh).1]
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  exact le_min hv hw

end
end Contingency.Grid

 

 

open Set MeasureTheory
open scoped BigOperators Pointwise
namespace Contingency.Dense
noncomputable section
variable {a c q K : ℕ}
open Contingency.Grid Contingency.Interpolation

def binExponent (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (d : ℝ) (x : Fin q → ℝ) : ℝ :=
  d^4*penalty R P w (d^8) d (fun s => x (e.symm s))

def binWeight (e : Fin q ≃ Fin a×Fin c) (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (d : ℝ) : Vertex q K → ℝ := exponentWeight (binExponent e R P w d)

theorem exponent_lipschitz (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 1 ≤ d) (he : (a*c:ℕ) ≤ d)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8)
    (x y : Fin q → ℝ) : |binExponent e R P w d x-binExponent e R P w d y| ≤ ‖x-y‖ := by
  have hd0 : 0<d := by linarith
  let u : Fin a×Fin c → ℝ := fun s => x (e.symm s)
  let v : Fin a×Fin c → ℝ := fun s => y (e.symm s)
  have hn : ‖u-v‖ ≤ ‖x-y‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro s
    exact norm_le_pi_norm (x-y) (e.symm s)
  have hh := penalty_difference R P w (d^8) d (d/d^8*‖u-v‖) (by positivity) u v
    (fun i j => normalized_lipschitz R P w (d^8) d (by positivity) he hR hP hRmax hPmax hw0 hw u v i j)
  have hcoef : d^4*(d/d^8) ≤ 1 := by
    have hid : d^4*(d/d^8)=1/d^3 := by field_simp
    rw [hid]
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ hd)
  unfold binExponent
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ d^4)]
  calc
    _ ≤ d^4*(d/d^8*‖u-v‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ ‖u-v‖ := by nlinarith only [mul_le_mul_of_nonneg_right hcoef (norm_nonneg (u-v))]
    _ ≤ _ := hn

theorem bin_density_eq (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (x : Fin q → ℝ) :
    (densityWeight e R P w (d^8) d (d^4) (by positivity)).f x=(2:ℝ)^(-binExponent e R P w d x) := by
  simp only [densityWeight,density,binExponent,neg_mul]

 

theorem bin_border_bound (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 1 ≤ d) (he : (a*c:ℕ) ≤ d) (hq : (q:ℝ) ≤ d) (hK : 1 ≤ K)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8)
    (V : Finset (Vertex q K)) (hV : V.Nonempty) (hVc : Vᶜ.Nonempty) :
    Real.log 2/(64*d*K)*min (∑ v∈V,binWeight e R P w d v) (∑ v∈Vᶜ,binWeight e R P w d v) ≤
      border V (binWeight e R P w d) := by
  let F := densityWeight e R P w (d^8) d (d^4) (by positivity)
  have hlip (x y : Fin q → ℝ) : |binExponent e R P w d x-binExponent e R P w d y| ≤ 1*‖x-y‖ := by
    simpa only [one_mul] using exponent_lipschitz e R P w d hd he hR hP hRmax hPmax hw0 hw x y
  apply border_bound F _ (fun v => (exponentWeight_pos _ v).le) d hd hq hK
  · intro x y α β ha hb hab
    exact densityWeight_logconcave e R P w (d^8) d (d^4) (by positivity) x y α β ha hb hab
  · intro v x hx
    rw [show F.f x=(2:ℝ)^(-binExponent e R P w d x) from bin_density_eq _ _ _ _ _ _]
    exact weight_bin_comparison _ 1 (by norm_num) le_rfl hlip v x hx
  · intro v w' i hn x hx
    rw [show F.f x=(2:ℝ)^(-binExponent e R P w d x) from bin_density_eq _ _ _ _ _ _]
    apply weight_face_comparison _ 1 (1/(4*d)) (by norm_num) (by
      have hd0 : 0<d := by linarith
      positivity) _ hlip v w' i hn x hx
    have hd0 : 0<d := by linarith
    have hfrac : 1/(4*d) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  · exact hV
  · exact hVc

 

theorem bin_conductance_numerator (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 1 ≤ d) (he : (a*c:ℕ) ≤ d) (hq : (q:ℝ) ≤ d) (hK : 1 ≤ K)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8)
    (p : ℝ) (hp : 1/(16*d) ≤ p)
    (V : Finset (Vertex q K)) (hV : V.Nonempty) (hVc : Vᶜ.Nonempty) :
    1/(100000*d^2*K)*min (∑ v∈V,binWeight e R P w d v) (∑ v∈Vᶜ,binWeight e R P w d v) ≤
      p*border V (binWeight e R P w d) := by
  have hd0 : 0<d := by linarith
  have hK0 : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have hb := bin_border_bound e R P w d hd he hq hK hR hP hRmax hPmax hw0 hw V hV hVc
  have hn : 0 ≤ border V (binWeight e R P w d) := by
    unfold border
    exact Finset.sum_nonneg fun v _ => le_min (exponentWeight_pos _ _).le (exponentWeight_pos _ _).le
  have hc : 1/(100000*d^2*K) ≤ (1/(16*d))*(Real.log 2/(64*d*K)) := by
    apply (div_le_iff₀ (by positivity : 0 < 100000*d^2*K)).mpr
    have hh : (1/(16*d))*(Real.log 2/(64*d*K))*(100000*d^2*K)=3125/32*Real.log 2 := by field_simp; norm_num
    rw [hh]
    linarith only [Real.log_two_gt_d9]
  have hmin : 0 ≤ min (∑ v∈V,binWeight e R P w d v) (∑ v∈Vᶜ,binWeight e R P w d v) :=
    le_min (Finset.sum_nonneg fun v _ => (exponentWeight_pos _ v).le) (Finset.sum_nonneg fun v _ => (exponentWeight_pos _ v).le)
  calc
    _ ≤ (1/(16*d))*(Real.log 2/(64*d*K))*min (∑ v∈V,binWeight e R P w d v) (∑ v∈Vᶜ,binWeight e R P w d v) := mul_le_mul_of_nonneg_right hc hmin
    _ ≤ (1/(16*d))*border V (binWeight e R P w d) := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hp hn

end
end Contingency.Dense

 

 

open Set MeasureTheory
open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c q K : ℕ}
open Contingency.Grid Contingency.Interpolation

theorem region_volume_pos (f : (Fin (a+1)×Fin (c+1)) → (Fin q → ℝ) → ℝ)
    (hf : ∀ i,Continuous (f i)) (u : Fin q → ℝ) (hu : ∀ i,0<f i u) :
    0 < volume (region f 0) := by
  let S := {x | ∀ i,0<f i x}
  have ho : IsOpen S := by
    have he : S=⋂ i,{x | 0<f i x} := by ext x; simp [S]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hf i)
  exact (ho.measure_pos volume ⟨u,hu⟩).trans_le (measure_mono (fun x hx i => (hx i).le))

theorem dense_density_volume (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 4 ≤ d) (hq : (q:ℝ) ≤ d) (u : Fin q → ℝ)
    (hu : ∀ i,1/(2*d) ≤ constraints e R P w i u) (S : Set (Fin q → ℝ)) :
    (∫⁻ x in S,ENNReal.ofReal ((densityWeight e R P w (d^8) d (d^4) (by positivity)).f x)) ≤
      4*volume (region (constraints e R P w) 0) := by
  let p (x : Fin q → ℝ) := penalty R P w (d^8) d (fun s => x (e.symm s))
  have hd0 : 0<d := by linarith
  apply density_layer_bound p ((penalty_continuous R P w (d^8) d).comp
    (continuous_pi fun _ => continuous_apply _)).measurable
    (fun x => penalty_nonneg _ _ _ _ _ _) (d^4) (by positivity) S
  intro j
  have hsub : {x | p x < ((j:ℝ)+1)/d^4} ∩ S ⊆
      region (constraints e R P w) (-(d/d^8+((j:ℝ)+1)/d^4)) := by
    intro x hx i
    have hh := le_penalty R P w (d^8) d (fun s => x (e.symm s)) i.1 i.2
    have hj := hx.1
    change p x < _ at hj
    change -constraints e R P w i x-d/d^8 ≤ p x at hh
    linarith only [hh,hj]
  calc
    _ ≤ volume (region (constraints e R P w) (-(d/d^8+((j:ℝ)+1)/d^4))) := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (2*d^2*(d/d^8+((j:ℝ)+1)/d^4)))*volume (region (constraints e R P w) 0) :=
      relaxed_volume_dense _ (constraints_affine e R P w) d hd0 hq u hu _ (by positivity)
    _ ≤ ENNReal.ofReal ((4/3:ℝ)^(j+1))*volume (region (constraints e R P w) 0) := by
      gcongr
      exact dense_exponent_layer d hd j
    _ = _ := by
      rw [ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
      norm_num

theorem dense_bin_normalizer_bound (e : Fin q ≃ Fin a×Fin c)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (d : ℝ) (hd : 4 ≤ d) (he : (a*c:ℕ) ≤ d) (hq : (q:ℝ) ≤ d)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j)
    (hRmax : ∀ i,R i ≤ R (Fin.last a)) (hPmax : ∀ j,P j ≤ P (Fin.last c))
    (hw0 : ∀ i j,0 ≤ w i j) (hw : ∀ i j,w i j ≤ scale R P i.castSucc j.castSucc/d^8)
    (u : Fin q → ℝ) (hu : ∀ i,1/(2*d) ≤ constraints e R P w i u) :
    ENNReal.ofReal (∑ v : Vertex q K,binWeight e R P w d v) ≤
      16*volume (region (constraints e R P w) 0) := by
  let F := densityWeight e R P w (d^8) d (d^4) (by positivity)
  let S := boxUnion (boxes (Finset.univ : Finset (Vertex q K)))
  have hlip (x y : Fin q → ℝ) : |binExponent e R P w d x-binExponent e R P w d y| ≤ 1*‖x-y‖ := by
    simpa only [one_mul] using exponent_lipschitz e R P w d (by linarith) he hR hP hRmax hPmax hw0 hw x y
  have hb : ∀ (v : Vertex q K) x,x∈(bin v).carrier → binWeight e R P w d v/4 ≤ F.f x ∧ F.f x ≤ 4*binWeight e R P w d v := by
    intro v x hx
    rw [show F.f x=(2:ℝ)^(-binExponent e R P w d x) from bin_density_eq _ _ _ _ _ _]
    exact weight_bin_comparison _ 1 (by norm_num) le_rfl hlip v x hx
  have hint := (boxes_integral_bounds F (binWeight e R P w d) hb Finset.univ).1
  have hsum : (∑ v : Vertex q K,binWeight e R P w d v) ≤ 4*(∫ x in S,F.f x) := by
    dsimp [S]
    simpa only [mul_comm] using (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mp hint
  calc
    _ ≤ ENNReal.ofReal (4*(∫ x in S,F.f x)) := ENNReal.ofReal_le_ofReal hsum
    _ = 4*(∫⁻ x in S,ENNReal.ofReal (F.f x)) := by
      rw [ENNReal.ofReal_mul (by norm_num),ofReal_integral_eq_lintegral_ofReal (F.integrable _) (Filter.Eventually.of_forall fun x => (F.positive x).le)]
      norm_num [S]
    _ ≤ 4*(4*volume (region (constraints e R P w) 0)) := by
      gcongr
      exact dense_density_volume e R P w d hd hq u hu S
    _ = _ := by rw [← mul_assoc]; norm_num

end
end Contingency.Dense

end

end OAI
