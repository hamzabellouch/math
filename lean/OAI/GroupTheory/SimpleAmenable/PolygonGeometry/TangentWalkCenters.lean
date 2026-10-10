import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.UniformPropagationBounds
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LabelShiftedCharts

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TangentWalkCenters

@[simp] theorem pointCoordinate_zero (j : Fin 2) : pointCoordinate (0 : CutRing × CutRing) j = 0 := by
  simp [pointCoordinate]

@[simp] theorem pointCoordinate_sub (z w : CutRing × CutRing) (j : Fin 2) :
    pointCoordinate (z-w) j = pointCoordinate z j-pointCoordinate w j := by
  fin_cases j <;> rfl

@[simp] theorem pointLabel_zero (j : Fin 2) : pointLabel (0 : CutRing × CutRing) j = 0 := by
  simp [pointLabel,endpointLabel]

@[simp] theorem pointLabel_sub (z w : CutRing × CutRing) (j : Fin 2) :
    pointLabel (z-w) j = pointLabel z j-pointLabel w j := by
  simp only [pointLabel,pointCoordinate_sub,endpointLabel_sub]

theorem tangentOffset_ordinary_bound (a : ℕ) (d : Fin 2) (w : CutRing) (j : Fin 2) :
    |ordinary (pointCoordinate (tangentOffset a d w) j)| ≤
      (1+|ordinary (cutTau^a)|)*|ordinary w| := by
  have h0 := abs_nonneg (ordinary w)
  have h1 := abs_nonneg (ordinary (cutTau^a))
  fin_cases d <;> fin_cases j
  · change |ordinary w| ≤ _
    nlinarith [mul_nonneg h0 h1]
  · change |ordinary (cutTau^a*w)| ≤ _
    rw [map_mul,abs_mul]
    nlinarith
  · change |ordinary (cutTau^a*w)| ≤ _
    rw [map_mul,abs_mul]
    nlinarith
  · change |ordinary w| ≤ _
    nlinarith [mul_nonneg h0 h1]

theorem tangentOffset_label_bound (a : ℕ) (d : Fin 2) (w : CutRing) (j : Fin 2) :
    |(pointLabel (tangentOffset a d w) j : ℝ)| ≤
      |(endpointLabel w : ℝ)|+|(endpointLabel (cutTau^a*w) : ℝ)| := by
  have h0 := abs_nonneg (endpointLabel w : ℝ)
  have h1 := abs_nonneg (endpointLabel (cutTau^a*w) : ℝ)
  fin_cases d <;> fin_cases j
  · exact le_add_of_nonneg_right h1
  · exact le_add_of_nonneg_left h0
  · exact le_add_of_nonneg_left h0
  · exact le_add_of_nonneg_right h1

theorem tangent_centers_uniform (a : ℕ) (u v : CutRing) (huv : u*v=1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ w : CutRing,
      |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w : ℝ)| ≤ B*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing),
      ∃ (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
        z 0 = z₀ ∧ z T = z₀+tangentOffset a d w ∧
        (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) ∧
        (∀ i j, |ordinary (pointCoordinate (z i-z₀) j)| ≤
          (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))) ∧
        (∀ i j, |(pointLabel (z i-z₀) j : ℝ)| ≤ K*(n:ℝ)) := by
  obtain ⟨K,hK,hwalk⟩ := tangent_chain_uniform (cutTau^a) u v huv hA hB
  refine ⟨K,hK,fun n hn w hw hw' d z₀ => ?_⟩
  obtain ⟨xs,hxs,hm,_hlen,ho,hq⟩ := hwalk n hn w hw hw'
  have he : ∀ i : ℕ, ∃ e : Fin 5, ∀ hi : i < xs.length, xs[i]'hi = signedShortSteps u e := by
    intro i
    by_cases hi : i < xs.length
    · obtain hh | hh | hh | hh := hm xs[i] (List.getElem_mem hi)
      · exact ⟨1,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨2,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨3,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨4,fun _ => by simpa [signedShortSteps] using hh⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose e he using he
  let z := fun i => z₀+tangentOffset a d (xs.take i).sum
  refine ⟨xs.length,z,e,?_,?_,?_,?_,?_⟩
  · simp [z]
  · simp [z,hxs]
  · intro i hi
    have hs : (xs.take (i+1)).sum = (xs.take i).sum+xs[i] := by
      rw [List.take_add_one]
      simp only [List.getElem?_eq_getElem hi,Option.toList_some,List.sum_append,List.sum_singleton]
    dsimp [z]
    rw [hs,he i hi,tangentOffset_add,add_assoc]
  · intro i j
    have hh := tangentOffset_ordinary_bound a d (xs.take i).sum j
    have hh' := mul_le_mul_of_nonneg_left (ho i) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|)
    simpa only [z,add_sub_cancel_left] using hh.trans hh'
  · intro i j
    simpa only [z,add_sub_cancel_left] using (tangentOffset_label_bound a d (xs.take i).sum j).trans (hq i)

end TangentWalkCenters

section UniformChartGeometry

theorem uniform_tangent_chart_geometry (a : ℕ) (u v s : CutRing) (huv : u*v=1)
    (hs : 0 < ordinary s)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {A B D E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (_hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ w : CutRing, |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ B*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing) (q p : Fin 2 → ℤ) (L V : Fin 2 → CutRing),
      (∀ j, |(pointLabel z₀ j+q j-p j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (L j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (V j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      ∃ (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
        z 0 = z₀ ∧ z T = z₀+tangentOffset a d w ∧
        (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) ∧
        (∀ i j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) ∧
        (∀ i j, -ordinary s+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-ordinary s/4) ∧
        (∀ i j, ordinary (V j)+ordinary s/4 ≤ ordinary s+ordinary (pointCoordinate (z i) j)) := by
  obtain ⟨K,hK,hwalk⟩ := tangent_centers_uniform a u v huv hA hB
  let H := (1+|ordinary (cutTau^a)|)*A+D
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (4*H/ordinary s))
  have hN1 : 1 ≤ N := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (by linarith : (1:ℝ) ≤ N)
  refine ⟨K+E,by linarith,N,hN1,?_⟩
  intro n hn w hw hw' d z₀ q p L V hp hL hV
  have hn1 : 1 ≤ n := hN1.trans hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hbig : 4*H/ordinary s < (n:ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hn'
  have hfrac : H/(n:ℝ) < ordinary s/4 := by
    have hh := (div_lt_iff₀ hs).mp hbig
    apply (div_lt_iff₀ hn0).mpr
    nlinarith
  obtain ⟨T,z,e,hz0,hzT,hstep,ho,hq⟩ := hwalk n hn1 w hw hw' d z₀
  refine ⟨T,z,e,hz0,hzT,hstep,?_,?_,?_⟩
  · intro i j
    have he : ((pointLabel (z i) j+q j-p j:ℤ):ℝ) =
        (pointLabel (z i-z₀) j:ℝ)+(pointLabel z₀ j+q j-p j:ℝ) := by
      simp only [pointLabel_sub,Int.cast_sub,Int.cast_add]
      ring
    rw [Nat.cast_natAbs,Int.cast_abs,he]
    calc
      _ ≤ |(pointLabel (z i-z₀) j:ℝ)|+|(pointLabel z₀ j+q j-p j:ℝ)| := abs_add_le _ _
      _ ≤ K*(n:ℝ)+E*(n:ℝ) := add_le_add (hq i j) (hp j)
      _ ≤ (K+E+1)*(n:ℝ) := by nlinarith
  · intro i j
    have hz := (abs_le.mp (ho i j)).2
    have hl := (abs_le.mp (hL j)).1
    simp only [pointCoordinate_sub,map_sub] at hz
    have he : (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))+D/(n:ℝ) =
        H/(n:ℝ)+(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) := by
      dsimp [H]
      ring
    linarith
  · intro i j
    have hz := (abs_le.mp (ho i j)).1
    have hv := (abs_le.mp (hV j)).2
    simp only [pointCoordinate_sub,map_sub] at hz
    have he : (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))+D/(n:ℝ) =
        H/(n:ℝ)+(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) := by
      dsimp [H]
      ring
    linarith

end UniformChartGeometry

end SimpleAmenable
end
end

end OAI
