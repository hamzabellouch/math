import Mathlib
import OAI.Probability.Perceptron.Pressure.HeightPartition

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

def extendedFieldExponents {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+2)) : ℝ :=
  ∑ r, if r.castSucc < i then w r else 0

def finiteFieldCDFLeft {d : ℕ} (w h : Fin (d+1) → ℝ) (t : ℝ) : ℝ :=
  ∑ r, if h r < t then w r else 0

lemma extendedFieldExponents_castSucc {d : ℕ} (w : Fin (d+1) → ℝ) (i : Fin (d+1)) :
    extendedFieldExponents w i.castSucc=fieldExponents w i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [extendedFieldExponents,fieldExponents]
  · unfold extendedFieldExponents fieldExponents
    simp only [Fin.cases_succ,stepCumulative]
    apply Finset.sum_congr rfl
    intro r _
    have he : r.castSucc < i.succ.castSucc ↔ r ≤ i.castSucc := by
      simp only [Fin.lt_def,Fin.le_def,Fin.val_castSucc,Fin.val_succ]
      omega
    simp only [he]

lemma extendedFieldExponents_last {d : ℕ} (w : Fin (d+1) → ℝ) :
    extendedFieldExponents w (Fin.last (d+1))=∑ r, w r := by
  simp [extendedFieldExponents,Fin.castSucc_lt_last]

lemma extendedFieldExponents_nonneg {d : ℕ} (w : Fin (d+1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (i : Fin (d+2)) : 0 ≤ extendedFieldExponents w i := by
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> first | exact hw r | rfl

lemma extendedFieldExponents_heightIndex {d : ℕ} (w h : Fin (d+1) → ℝ) (hh : Monotone h)
    (t : ℝ) : extendedFieldExponents w (heightIndex h t)=finiteFieldCDFLeft w h t := by
  simp only [extendedFieldExponents,finiteFieldCDFLeft,lt_heightIndex_iff h hh]

lemma sphericalHeatValue_compress (n N : ℕ) (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (l : List (Fin N×ℝ)) (hl : l.Pairwise (fun a b => a.1 ≤ b.1))
    (hv : ∀ c ∈ l, 0 ≤ c.2) :
    sphericalHeatValue n (l.map fun c => (p c.1,Real.sqrt c.2))=
      sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (gridVariance l i))) := by
  unfold sphericalHeatValue
  rw [gaussianBackward_compress (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ))) N p hp l hl hv]
  congr 1
  rw [List.map_ofFn,List.sum_ofFn,List.map_map]
  change (l.map fun c => (Real.sqrt c.2)^2).sum/2=(∑ i, (Real.sqrt (gridVariance l i))^2)/2
  simp only [Real.sq_sqrt (gridVariance_nonneg l hv _)]
  rw [gridVariance_sum]
  congr 2
  apply List.map_congr_left
  intro c hc
  exact Real.sq_sqrt (hv c hc)

lemma sphericalHeatValue_drop_last_one (n d : ℕ) (p v : Fin (d+2) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hv : ∀ i, 0 ≤ v i) (hpl : p (Fin.last (d+1))=1) :
    sphericalHeatValue n (List.ofFn fun i => (p i,Real.sqrt (v i)))=
      sphericalHeatValue n (List.ofFn fun i : Fin (d+1) => (p i.castSucc,Real.sqrt (v i.castSucc))) := by
  unfold sphericalHeatValue
  have he := congrFun (gaussianGrid_spherical_last n d p v hp (hv _) hpl) 0
  unfold gaussianGrid at he
  rw [he]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,Real.sq_sqrt (hv _)]
  rw [Fin.sum_univ_castSucc v]
  have hn : (n+1:ℕ) ≠ (0:ℝ) := by positivity
  field_simp [hn]
  ring

lemma finiteSphericalFieldValue_height_word {d K : ℕ} (w h : Fin (d+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0)
    (z : Fin (K+1) → ℝ) (hz : Monotone z) (hz0 : z 0=0)
    (hm : ∀ i, h i ∈ Set.range z) (n : ℕ) :
    finiteSphericalFieldValue n d w h=sphericalHeatValue n
      (List.ofFn fun j => (finiteFieldCDFLeft w h (z j.succ),Real.sqrt (heightVariances z j))) := by
  let l := List.ofFn fun j => (heightIndex h (z j.succ),heightVariances z j)
  have hl : l.Pairwise (fun a b => a.1 ≤ b.1) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact heightIndex_monotone h (hz (Fin.succ_le_succ_iff.mpr hij.le))
  have hv : ∀ c ∈ l, 0 ≤ c.2 := by
    intro c hc; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
    exact heightVariances_nonneg z hz j
  have he := sphericalHeatValue_compress n (d+2) (extendedFieldExponents w)
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) l hl hv
  dsimp only [l] at he
  simp only [List.map_ofFn,Function.comp_def,extendedFieldExponents_heightIndex w h hh] at he
  rw [he,sphericalHeatValue_drop_last_one n d _ _
    (extendedFieldExponents_nonneg w (fun i => (hw i).le)) (gridVariance_nonneg l hv)
    (by rw [extendedFieldExponents_last,hw1])]
  have hvf : (fun i => gridVariance l i.castSucc)=fieldVariances d h := by
    have hpref : varianceLevels (fun i => gridVariance l i.castSucc)=h := by
      funext i
      exact heightIndex_grid_prefix h hh z hz hz0 hm i
    rw [← hpref,fieldVariances_varianceLevels]
  simp only [extendedFieldExponents_castSucc]
  change finiteSphericalFieldValue n d w h=sphericalHeatValue n
    (List.ofFn fun i => (fieldExponents w i,Real.sqrt ((fun i => gridVariance l i.castSucc) i)))
  rw [hvf]
  exact finiteSphericalFieldValue_eq_heat w h hw hw1 hh hh0 n

def heightIndicator (r t : ℝ) : ℝ := if r < t then 1 else 0

lemma heightIndicator_antitone (t : ℝ) : Antitone (fun r => heightIndicator r t) := by
  intro r s hrs
  dsimp only [heightIndicator]
  split_ifs with hs hr
  · rfl
  · exact (hr (hrs.trans_lt hs)).elim
  · norm_num
  · rfl

lemma heightIndicator_weighted_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r : ℝ) (hr : r ∈ Set.range z) :
    (∑ j, heightVariances z j*heightIndicator r (z j.succ))=2*(z (Fin.last K)-r) := by
  have he (j : Fin K) : heightVariances z j*heightIndicator r (z j.succ)=
      heightVariances z j-(if z j.succ ≤ r then heightVariances z j else 0) := by
    unfold heightIndicator
    by_cases hj : z j.succ ≤ r
    · simp [hj,not_lt.mpr hj]
    · simp [hj,lt_of_not_ge hj]
  simp only [he,Finset.sum_sub_distrib,heightVariances_prefix z hz r hr,heightVariances_sum]
  ring

lemma heightIndicator_distance_sum {K : ℕ} (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (r s : ℝ) (hr : r ∈ Set.range z) (hs : s ∈ Set.range z) :
    (∑ j, heightVariances z j*|heightIndicator r (z j.succ)-heightIndicator s (z j.succ)|)=
      2*|r-s| := by
  have H (a b : ℝ) (ha : a ∈ Set.range z) (hb : b ∈ Set.range z) (hab : a ≤ b) :
      (∑ j, heightVariances z j*|heightIndicator a (z j.succ)-heightIndicator b (z j.succ)|)=
        2*|a-b| := by
    simp only [abs_of_nonneg (sub_nonneg.mpr (heightIndicator_antitone _ hab)),mul_sub,
      Finset.sum_sub_distrib,heightIndicator_weighted_sum z hz a ha,heightIndicator_weighted_sum z hz b hb]
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  rcases le_total r s with hrs | hsr
  · exact H r s hr hs hrs
  · simpa only [abs_sub_comm] using H s r hs hr hsr

lemma finiteFieldCDFLeft_coupling_sub {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t=
      ∑ a, c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t) := by
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [coupling_sum_fst c w (fun i => heightIndicator (h i) t) hr,
    coupling_sum_snd c v (fun j => heightIndicator (g j) t) hc]
  simp only [finiteFieldCDFLeft,heightIndicator,mul_ite,mul_one,mul_zero]

lemma finiteFieldCDFLeft_coupling_abs {d e : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j) (t : ℝ) :
    |finiteFieldCDFLeft w h t-finiteFieldCDFLeft v g t| ≤
      ∑ a, c a*|heightIndicator (h a.1) t-heightIndicator (g a.2) t| := by
  rw [finiteFieldCDFLeft_coupling_sub w h v g c hr hc t]
  simpa only [abs_mul,abs_of_nonneg (hcn _)] using
    Finset.abs_sum_le_sum_abs (fun a => c a*(heightIndicator (h a.1) t-heightIndicator (g a.2) t)) Finset.univ

lemma finiteFieldCDFLeft_partition_cost {d e K : ℕ} (w h : Fin (d+1) → ℝ)
    (v g : Fin (e+1) → ℝ) (c : Fin (d+1)×Fin (e+1) → ℝ)
    (hcn : ∀ a, 0 ≤ c a) (hr : ∀ i, ∑ j, c (i,j)=w i) (hc : ∀ j, ∑ i, c (i,j)=v j)
    (z : Fin (K+1) → ℝ) (hz : Monotone z)
    (hm : ∀ i, h i ∈ Set.range z) (gm : ∀ j, g j ∈ Set.range z) :
    (∑ j, heightVariances z j*|finiteFieldCDFLeft w h (z j.succ)-finiteFieldCDFLeft v g (z j.succ)|) ≤
      2*(∑ a, c a*|h a.1-g a.2|) := by
  calc
    _ ≤ ∑ j, heightVariances z j*(∑ a, c a*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (finiteFieldCDFLeft_coupling_abs w h v g c hcn hr hc _)
        (heightVariances_nonneg z hz j)
    _ = ∑ a, c a*(∑ j, heightVariances z j*
        |heightIndicator (h a.1) (z j.succ)-heightIndicator (g a.2) (z j.succ)|) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [heightIndicator_distance_sum z hz _ _ (hm _) (gm _),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

lemma exists_common_height_partition {I J : Type*} [Fintype I] [Fintype J]
    (h : I → ℝ) (g : J → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ i, h i ∈ Icc (0:ℝ) H) (hg : ∀ j, g j ∈ Icc (0:ℝ) H) :
    ∃ (K : ℕ) (z : Fin (K+1) → ℝ), Monotone z ∧ z 0=0 ∧ z (Fin.last K)=H ∧
      (∀ i, h i ∈ Set.range z) ∧ (∀ j, g j ∈ Set.range z) := by
  classical
  let S : Finset ℝ := insert 0 (insert H (Finset.univ.image h ∪ Finset.univ.image g))
  have hs0 : (0:ℝ) ∈ S := by simp [S]
  have hsH : H ∈ S := by simp [S]
  have hsb : ∀ x ∈ S, x ∈ Icc (0:ℝ) H := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with rfl | rfl | ⟨i,rfl⟩ | ⟨j,rfl⟩
    · exact ⟨le_rfl,hH⟩
    · exact ⟨hH,le_rfl⟩
    · exact hh i
    · exact hg j
  obtain ⟨K,hK⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0,hs0⟩)
  let e := S.orderIsoOfFin hK
  let z : Fin (K+1) → ℝ := fun i => e i
  have hz : Monotone z := fun i j hij => e.monotone hij
  have hm (x : ℝ) (hx : x ∈ S) : x ∈ Set.range z := by
    exact ⟨e.symm ⟨x,hx⟩,congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩
  have hz0 : z 0=0 := by
    obtain ⟨i,hi⟩ := hm 0 hs0
    apply le_antisymm
    · rw [← hi]; exact hz (Fin.zero_le i)
    · exact (hsb (z 0) (e 0).2).1
  have hzH : z (Fin.last K)=H := by
    obtain ⟨i,hi⟩ := hm H hsH
    apply le_antisymm
    · exact (hsb (z (Fin.last K)) (e (Fin.last K)).2).2
    · rw [← hi]; exact hz (Fin.le_last i)
  exact ⟨K,z,hz,hz0,hzH,(fun i => hm (h i) (by simp [S])),(fun j => hm (g j) (by simp [S]))⟩

end SphericalPerceptronFreeEnergy

end

end OAI
