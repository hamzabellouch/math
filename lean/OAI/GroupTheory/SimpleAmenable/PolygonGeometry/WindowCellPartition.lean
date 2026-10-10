import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.TangentRectangleCommutation
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowCells

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WindowCellPartition

theorem finite_interval_cell {n : ℕ} {x : Fin (n+1) → ℝ}
    (_hn : 1 ≤ n) (t : ℝ) (hl : x 0 ≤ t) (hu : t < x (Fin.last n)) :
    ∃ i : Fin n, x i.castSucc ≤ t ∧ t < x i.succ := by
  classical
  let S : Finset (Fin (n+1)) := Finset.univ.filter fun i => x i ≤ t
  have hS : S.Nonempty := ⟨0,by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hl⟩
  let i := S.max' hS
  have hi : x i ≤ t := (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
  have hin : i.val < n := by
    have hil : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    by_contra hh
    have he : i = Fin.last n := Fin.ext (by change i.val = n; omega)
    rw [he] at hi
    linarith
  refine ⟨⟨i.val,hin⟩,hi,?_⟩
  by_contra hh
  have hj : (⟨i.val+1,by omega⟩ : Fin (n+1)) ∈ S := by
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    exact le_of_not_gt hh
  have he := Finset.le_max' S _ hj
  change i.val+1 ≤ i.val at he
  omega

noncomputable def windowCell (a : ℕ) (j : Fin 2) (n : ℕ) (q : ℤ) (i : Fin n) :
    polygonAlgebra a := coordinateInterval a j (windowCut n q i.castSucc) (windowCut n q i.succ)

noncomputable def liftedCoordinate {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) : ℝ :=
  coordinate j p - (⌊coordinate j p-ordinary z⌋:ℤ)

theorem liftedCoordinate_bounds {a : ℕ} (j : Fin 2) (z : CutRing) (p : GenericSquare a) :
    ordinary z ≤ liftedCoordinate j z p ∧ liftedCoordinate j z p < ordinary z+1 := by
  have hh := Int.fract_nonneg (coordinate j p-ordinary z)
  have hh' := Int.fract_lt_one (coordinate j p-ordinary z)
  simp only [Int.fract,liftedCoordinate] at *
  constructor <;> linarith

theorem windowCell_mem {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (i : Fin n) (p : GenericSquare a) :
    p ∈ (windowCell a j n q i).val ↔
      ordinary (windowCut n q i.castSucc) ≤ liftedCoordinate j ((q:CutRing)*cutTau) p ∧
      liftedCoordinate j ((q:CutRing)*cutTau) p < ordinary (windowCut n q i.succ) := by
  have hn' : (200:ℝ) < n := by exact_mod_cast (by omega : 200 < n)
  have hlen : ordinary (windowCut n q i.succ)-ordinary (windowCut n q i.castSucc) < 1 :=
    (windowCut_mesh n q i).trans_lt ((div_lt_one (by linarith)).mpr hn')
  have hord := (windowCut_strictMono n q (Fin.castSucc_lt_succ (i := i))).le
  change p ∈ coordinateBetween _ _ _ _ ↔ _
  rw [mem_coordinateBetween_iff j _ _ hord hlen p]
  constructor
  · rintro ⟨k,hk,hk'⟩
    have hb := windowCut_bounds n q i.castSucc
    have hb' := windowCut_bounds n q i.succ
    have hfloor : (⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋:ℤ) = -k := by
      apply Int.floor_eq_iff.mpr
      simp only [Int.cast_neg]
      constructor <;> linarith
    simp only [liftedCoordinate,hfloor,Int.cast_neg,sub_neg_eq_add]
    exact ⟨hk,hk'⟩
  · rintro ⟨hl,hu⟩
    refine ⟨-⌊coordinate j p-ordinary ((q:CutRing)*cutTau)⌋,?_,?_⟩
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hl
    · simpa only [Int.cast_neg,sub_eq_add_neg,liftedCoordinate] using hu

theorem windowCell_cover {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ)
    (p : GenericSquare a) : ∃ i : Fin n, p ∈ (windowCell a j n q i).val := by
  have hb := liftedCoordinate_bounds j ((q:CutRing)*cutTau) p
  have hz := windowCut_zero n q (by omega)
  have hh := windowCut_last n q
  obtain ⟨i,hi⟩ := finite_interval_cell (x := fun i => ordinary (windowCut n q i))
    (by omega) (liftedCoordinate j ((q:CutRing)*cutTau) p)
    (by simpa only [hz] using hb.1) (by simpa only [hh,map_add,map_one] using hb.2)
  exact ⟨i,(windowCell_mem j n hn q i p).mpr hi⟩

theorem windowCell_pairwise_disjoint {a : ℕ} (j : Fin 2) (n : ℕ) (hn : 201 ≤ n) (q : ℤ) :
    Pairwise fun i k : Fin n => Disjoint (windowCell a j n q i).val (windowCell a j n q k).val := by
  intro i k hik
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hi := (windowCell_mem j n hn q i p).mp hp
  have hk := (windowCell_mem j n hn q k p).mp hp'
  rcases lt_or_gt_of_ne hik with hh | hh
  · have he := (windowCut_strictMono n q).monotone
      (show i.succ ≤ k.castSucc from by change i.val+1 ≤ k.val; change i.val < k.val at hh; omega)
    linarith
  · have he := (windowCut_strictMono n q).monotone
      (show k.succ ≤ i.castSucc from by change k.val+1 ≤ i.val; change k.val < i.val at hh; omega)
    linarith

end WindowCellPartition

section SeparatedOldRectangles

noncomputable def orientedPoint (d : Fin 2) (x y : CutRing) : CutRing × CutRing :=
  if d=0 then (x,y) else (y,x)

@[simp] theorem orientedPoint_coordinate (d j : Fin 2) (x y : CutRing) :
    pointCoordinate (orientedPoint d x y) j = if j=d then x else y := by
  fin_cases d <;> fin_cases j <;> simp [orientedPoint,pointCoordinate]

@[simp] theorem orientedPoint_label (d j : Fin 2) (x y : CutRing) :
    pointLabel (orientedPoint d x y) j = if j=d then endpointLabel x else endpointLabel y := by
  simp only [pointLabel,orientedPoint_coordinate]
  split <;> rfl

@[simp] theorem orientedPoint_tangent (a : ℕ) (d : Fin 2) (x y b : CutRing) :
    orientedPoint d x y+tangentOffset a d (b-x) = orientedPoint d b (y+cutTau^a*(b-x)) := by
  fin_cases d <;> simp [orientedPoint,tangentOffset]

structure OldStripPair (n : ℕ) (d : Fin 2) where
  left : LabelledRectangle n
  right : LabelledRectangle n
  lo : CutRing
  cutLeft : CutRing
  cutRight : CutRing
  hi : CutRing
  bottom : CutRing
  top : CutRing
  left_lower : ∀ j, left.lower j = if j=d then lo else bottom
  left_upper : ∀ j, left.upper j = if j=d then cutLeft else top
  right_lower : ∀ j, right.lower j = if j=d then cutRight else bottom
  right_upper : ∀ j, right.upper j = if j=d then hi else top
  ordered_left : ordinary lo ≤ ordinary cutLeft
  ordered_gap : ordinary cutLeft < ordinary cutRight
  ordered_right : ordinary cutRight ≤ ordinary hi
  ordered_cross : ordinary bottom ≤ ordinary top
  left_length : ∀ j, left.length j ≤ if j=d then n*9/10 else n/4
  right_length : ∀ j, right.length j ≤ if j=d then n*9/10 else n/4

namespace OldStripPair
variable {n : ℕ} {d : Fin 2} (P : OldStripPair n d)

noncomputable def displacement : CutRing := P.cutRight-P.cutLeft

noncomputable def firstCenter : CutRing × CutRing := orientedPoint d P.cutLeft P.bottom

@[simp] theorem displacement_ordinary : ordinary P.displacement = ordinary P.cutRight-ordinary P.cutLeft := by
  simp [displacement]

theorem left_center_label (j : Fin 2) :
    P.left.start j ≤ pointLabel P.firstCenter j ∧
      pointLabel P.firstCenter j < P.left.start j+P.left.length j := by
  simp only [firstCenter,orientedPoint_label]
  by_cases hj : j=d
  · simpa only [P.left_upper j,ite_eq_left hj] using P.left.upper_label j
  · simpa only [P.left_lower j,ite_eq_right hj] using P.left.lower_label j

theorem right_base_label (j : Fin 2) :
    P.right.start j ≤ pointLabel (orientedPoint d P.cutRight P.bottom) j ∧
      pointLabel (orientedPoint d P.cutRight P.bottom) j < P.right.start j+P.right.length j := by
  simpa only [orientedPoint_label,P.right_lower j,apply_ite] using P.right.lower_label j

end OldStripPair

theorem int_natAbs_le_div_succ (z : ℤ) (n : ℕ) (hz : |(z:ℝ)| < (n:ℝ)/10) :
    z.natAbs ≤ n/10+1 := by
  have hh : n < (n/10+1)*10 := by omega
  have hh' : (n:ℝ) < ((n/10+1:ℕ):ℝ)*10 := by exact_mod_cast hh
  have ha : (z.natAbs:ℝ) = |(z:ℝ)| := by simp
  have hb : (z.natAbs:ℝ) < ((n/10+1:ℕ):ℝ) := by rw [ha]; linarith
  exact_mod_cast hb.le

namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem separated_old_rectangles_commute (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u v : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (huv : u*v=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {C : ℝ} (hC : 0 ≤ C) (hSlope : 8*C < ordinary (cutTau^a))
    (hconj : |conjugate (cutTau^a)| < 1/1000) :
    ∃ N : ℕ, 201 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (_h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u),
      ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (d : Fin 2) (P : OldStripPair n d),
      ordinary P.hi-ordinary P.lo ≤ C/(n:ℝ) →
      ordinary P.top-ordinary P.bottom ≤ C/(n:ℝ) →
      |(endpointLabel P.displacement:ℝ)| ≤ 6*(n:ℝ)/5 →
      ∀ x y, Commute (B.rectangleCopy (by omega) g P.left x)
        (B.rectangleCopy (by omega) g P.right y) := by
  obtain ⟨N₀,hN₀,hcomm⟩ := tangent_rectangle_commutation_uniform
    (a := a) (hm := hm) hlarge hr s u v hs hsr huv hshort hC
    (show (0:ℝ) ≤ 6/5 by norm_num) hC (show (0:ℝ) ≤ 2 by norm_num)
  obtain ⟨N₁,hN₁,hlabel⟩ := contracted_transverse_label (cutTau^a) hconj hC
  obtain ⟨N₂,hN₂⟩ := fixed_chart_margin_eventually (endpointLabel s).natAbs
  obtain ⟨N₃,hN₃⟩ := transverse_chart_margin_eventually (endpointLabel s).natAbs
  obtain ⟨N₄,hN₄⟩ := exists_nat_gt (max C ((1+ordinary (cutTau^a))*C/ordinary s))
  refine ⟨max 201 (max N₀ (max N₁ (max N₂ (max N₃ (max N₄ (endpointLabel s).natAbs))))),by omega,?_⟩
  intro M B h n hn g d P hwid hheight hdisp
  have hn₀ : N₀ ≤ n := by omega
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have hn₄ : N₄ ≤ n := by omega
  have hnb : (endpointLabel s).natAbs ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlam : 0 < ordinary (cutTau^a) := by linarith
  have hnC : C < (n:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN₄).trans_le (by exact_mod_cast hn₄)
  have hnmargin : (1+ordinary (cutTau^a))*C/ordinary s < (n:ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hN₄).trans_le (by exact_mod_cast hn₄)
  have hsmall : (1+ordinary (cutTau^a))*C/(n:ℝ) < ordinary s := by
    apply (div_lt_iff₀ hnpos).mpr
    have hh := (div_lt_iff₀ hs).mp hnmargin
    nlinarith
  have hCn : C/(n:ℝ) < ordinary s := by
    have hh : 0 ≤ ordinary (cutTau^a)*C/(n:ℝ) := by positivity
    rw [add_mul,one_mul,add_div] at hsmall
    linarith
  have hlamCn : ordinary (cutTau^a)*(C/(n:ℝ)) < ordinary s := by
    have hh : 0 ≤ C/(n:ℝ) := by positivity
    rw [add_mul,one_mul,add_div] at hsmall
    rw [← mul_div_assoc]
    linarith
  have hdpos : 0 < ordinary P.displacement := by rw [P.displacement_ordinary]; linarith [P.ordered_gap]
  have hd : |ordinary P.displacement| ≤ C/(n:ℝ) := by
    rw [abs_of_pos hdpos,P.displacement_ordinary]
    linarith [P.ordered_left,P.ordered_right]
  have hdlabel := hlabel n hn₁ P.displacement hdisp (hd.trans (by gcongr; linarith))
  have hdnat := int_natAbs_le_div_succ _ n hdlabel
  have hgap : 1/(8*(n:ℝ)) ≤ ordinary P.displacement := by
    have hh := endpoint_separation (z := P.displacement) (by intro he; rw [he,map_zero] at hdpos; linarith)
      (n := 2*n) (by omega) (hd.trans ((div_le_one hnpos).mpr hnC.le))
      (show |(endpointLabel P.displacement:ℝ)| ≤ (2*n:ℕ) by push_cast; linarith)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat,abs_of_pos hdpos,← mul_assoc] at hh
    exact hh
  have hseparate : ordinary P.top-ordinary P.bottom < ordinary (cutTau^a*P.displacement) := by
    rw [map_mul]
    calc
      _ ≤ C/(n:ℝ) := hheight
      _ = (8*C)/(8*(n:ℝ)) := by ring
      _ < ordinary (cutTau^a)/(8*(n:ℝ)) := div_lt_div_of_pos_right hSlope (by positivity)
      _ = ordinary (cutTau^a)*(1/(8*(n:ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap hlam.le
  have hshift : ordinary (cutTau^a*P.displacement) < ordinary s := by
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_left (by simpa only [abs_of_pos hdpos] using hd) hlam.le).trans_lt hlamCn
  have hfit : Nonempty (P.left.ChartFit s P.firstCenter) := by
    apply P.left.chartFit_of_near_labels s P.firstCenter (fun j => pointLabel P.firstCenter j) 0
      P.left_center_label
    · intro j; simp
    · intro j
      have hp := P.left_length j
      have hh : n/4 ≤ n*9/10 := by omega
      have hh' := hN₂ n hn₂
      split_ifs at hp <;> simp only [Pi.zero_apply,mul_zero,add_zero] <;> omega
  have hfit' : Nonempty (P.right.ChartFit s (P.firstCenter+tangentOffset a d P.displacement)) := by
    have he : P.firstCenter+tangentOffset a d P.displacement =
        orientedPoint d P.cutRight (P.bottom+cutTau^a*P.displacement) := by
      exact orientedPoint_tangent a d P.cutLeft P.bottom P.cutRight
    rw [he]
    apply P.right.chartFit_of_near_labels s _ (fun j => pointLabel (orientedPoint d P.cutRight P.bottom) j)
      (fun j => if j=d then 0 else n/10+1) P.right_base_label
    · intro j
      simp only [orientedPoint_label]
      by_cases hj : j=d
      · simp [hj]
      · simpa only [ite_eq_right hj,endpointLabel_add,add_sub_cancel_left] using hdnat
    · intro j
      have hp := P.right_length j
      by_cases hj : j=d
      · simp only [ite_eq_left hj] at hp ⊢
        have hh := hN₂ n hn₂
        omega
      · simp only [ite_eq_right hj] at hp ⊢
        have hh := hN₃ n hn₃
        omega
  apply hcomm M B h n hn₀ g P.left P.right P.displacement hd (by nlinarith [hdisp]) d P.firstCenter
  · intro j
    have hh := P.left_center_label j
    have hl := P.left.length_le j
    have hh' : |pointLabel P.firstCenter j+symmetricWindowStart s j-P.left.start j| ≤ (2*n:ℕ) := by
      simp only [symmetricWindowStart]
      apply abs_le.mpr
      constructor <;> omega
    exact_mod_cast hh'
  · intro j
    simp only [P.left_lower j,OldStripPair.firstCenter,orientedPoint_coordinate]
    by_cases hj : j=d
    · simp only [ite_eq_left hj]
      rw [abs_of_nonpos (by linarith [P.ordered_left])]
      linarith [P.ordered_gap,P.ordered_right]
    · simp only [ite_eq_right hj,sub_self,abs_zero]; positivity
  · intro j
    simp only [P.left_upper j,OldStripPair.firstCenter,orientedPoint_coordinate]
    by_cases hj : j=d
    · simp only [ite_eq_left hj,sub_self,abs_zero]; positivity
    · simp only [ite_eq_right hj]
      rw [abs_of_nonneg (by linarith [P.ordered_cross])]
      exact hheight
  · exact hfit
  · exact hfit'
  · intro j
    simp only [signQuadrantLower,P.left_lower j,OldStripPair.firstCenter,orientedPoint_coordinate,ite_true]
    by_cases hj : j=d
    · simp only [ite_eq_left hj,map_neg]
      linarith [P.ordered_gap,P.ordered_right]
    · simp [hj]
  · intro j
    simp only [signQuadrantUpper,P.left_upper j,OldStripPair.firstCenter,orientedPoint_coordinate,ite_true]
    by_cases hj : j=d
    · simp [hj]
    · simp only [ite_eq_right hj]; linarith
  · intro j
    have he : P.firstCenter+tangentOffset a d P.displacement =
        orientedPoint d P.cutRight (P.bottom+cutTau^a*P.displacement) :=
      orientedPoint_tangent a d P.cutLeft P.bottom P.cutRight
    rw [he]
    simp only [signQuadrantLower,P.right_lower j,orientedPoint_coordinate,Bool.false_eq_true,ite_false]
    by_cases hj : j=d
    · simp [hj]
    · simp only [ite_eq_right hj,map_neg,map_add]; linarith
  · intro j
    have he : P.firstCenter+tangentOffset a d P.displacement =
        orientedPoint d P.cutRight (P.bottom+cutTau^a*P.displacement) :=
      orientedPoint_tangent a d P.cutLeft P.bottom P.cutRight
    rw [he]
    simp only [signQuadrantUpper,P.right_upper j,orientedPoint_coordinate,Bool.false_eq_true,ite_false]
    by_cases hj : j=d
    · simp only [ite_eq_left hj]; linarith [P.ordered_left,P.ordered_gap]
    · simp only [ite_eq_right hj,map_zero,zero_add,map_add]; linarith

end InitialCoverSystem
end SeparatedOldRectangles

end SimpleAmenable
end
end

end OAI
