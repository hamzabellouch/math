import OAI.Analysis.StrictMeans.CompactMorseEuler

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma source_morse_sign {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    {z : UpperHalfPlane} (hg : criticalMap k (halfPlaneFunction f) z=ξ) :
    Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z =
      if jacobianExpression k (halfPlaneFunction f) z<0 then 1 else -1 := by
  have hz := z.im_pos
  have hF := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have hd := halfPlaneFunction_deriv_ne_zero f hz
  have hp : halfPlaneFunction f z≠ξ := fun he=>criticalMap_ne_image hk.ne' hz hd (hg.trans he.symm)
  have hpos : 0<4*(squaredReciprocalPotential k (halfPlaneFunction f) ξ z)^2*(k^4/z.im^4) := by
    rw [squaredReciprocalPotential_eq_exp hz hp]
    positivity
  unfold Grid.morseSign
  rw [squaredReciprocalPotential_hessian_det hk.ne' hz hF hd hg]
  congr 1
  apply propext
  constructor
  · intro h
    exact ((mul_pos_iff.mp h).resolve_left (fun h' =>
      (not_lt_of_gt (neg_neg_of_pos hpos)) h'.1)).2
  · intro h
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hpos) h

lemma criticalCut_morse_sum {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    ∑ z∈(goodPair_criticalCut_finite hk hg hh).toFinset,
      Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z =
        ((maximaCut k f ξ h).ncard : ℤ)-(saddleCut k f ξ h).ncard := by
  classical
  let T := (goodPair_criticalCut_finite hk hg hh).toFinset
  have hsum : (∑ z∈T, Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z)=
      ∑ z∈T, if jacobianExpression k (halfPlaneFunction f) z<0 then (1:ℤ) else -1 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    exact source_morse_sign hk hz'.1
  have hm : T.filter (fun z : UpperHalfPlane=>jacobianExpression k (halfPlaneFunction f) z<0)=
      (maximaCut_finite hk hg hh).toFinset := by
    ext z
    simp [T,maximaCut]
  have hs : T.filter (fun z : UpperHalfPlane=>¬jacobianExpression k (halfPlaneFunction f) z<0)=
      (saddleCut_finite hk hg hh).toFinset := by
    ext z
    simp only [T,Finset.mem_filter,Set.Finite.mem_toFinset,saddleCut,Set.mem_ofPred_eq]
    apply and_congr_right
    intro hz
    rw [not_lt]
    exact ⟨fun hh => lt_of_le_of_ne hh (Ne.symm (hg.2.1 z hz.1)),le_of_lt⟩
  rw [hsum,Finset.sum_ite,hm,hs]
  rw [Set.ncard_eq_toFinset_card _ (maximaCut_finite hk hg hh),Set.ncard_eq_toFinset_card _ (saddleCut_finite hk hg hh)]
  simp [sub_eq_add_neg]

lemma goodPair_superlevel_count {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    (saddleCut k f ξ h).ncard≤(maximaCut k f ξ h).ncard := by
  classical
  by_cases hne : (saddleCut k f ξ h).Nonempty
  · obtain ⟨a,ha,hah,hcut,hstrict⟩ := goodPair_lower_regular_cut hk hg hh
    let u := squaredReciprocalPotential k (halfPlaneFunction f) ξ
    let K : Set ℂ := {z | 0<z.im ∧ u z≤(1/a)^2}
    let T := (goodPair_criticalCut_finite hk hg hh).toFinset
    let P := (source_poles_subsingleton f ξ).finite.toFinset
    let B : Finset ℂ := T.image UpperHalfPlane.coe
    let C := B∪P
    have hT (z : UpperHalfPlane) : z∈T ↔ z∈criticalCut k f ξ h := Set.Finite.mem_toFinset _
    have hP (z : ℂ) : z∈P ↔ 0<z.im ∧ halfPlaneFunction f z=ξ := Set.Finite.mem_toFinset _
    have hK : IsCompact K := by
      change IsCompact {z : ℂ | 0<z.im ∧ squaredReciprocalPotential k (halfPlaneFunction f) ξ z≤(1/a)^2}
      rw [squaredReciprocalPotential_sublevel ha]
      exact hg.1 a ha
    have hU (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ 2 u z :=
      (squaredReciprocalPotential_contDiffAt hz
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz))).of_le (by simp)
    have htr (z : ℂ) (hz : 0<z.im) : 0<Grid.second u z 1 1+Grid.second u z I I := by
      rw [← realHessian_eq_second (hU z hz),← realHessian_eq_second (hU z hz)]
      exact squaredReciprocalPotential_laplacian_pos hk hz
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz))
        (halfPlaneFunction_deriv_ne_zero f hz)
    have hBint (z : UpperHalfPlane) (hz : z∈T) : (z:ℂ)∈interior K :=
      source_squared_interior z.im_pos (source_squared_critical_strict hk ha
        ((hT z).mp hz).1 (hstrict z ((hT z).mp hz)))
    have hCint : ∀ z∈C, z∈interior K := by
      intro z hz
      rcases Finset.mem_union.mp hz with hb|hp
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
        exact hBint w hw
      · have hp' := (hP z).mp hp
        apply source_squared_interior hp'.1
        have hu0 : u z=0 := by simp [u,squaredReciprocalPotential,hp'.2]
        change u z < (1/a)^2
        rw [hu0]
        exact sq_pos_of_pos (one_div_pos.mpr ha)
    have hc : ∀ z, z∈K → (fderiv ℝ u z=0 ↔ z∈C) := by
      intro z hz
      rw [squaredReciprocalPotential_critical_iff hk.ne' hz.1
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz.1))]
      constructor
      · intro hh
        rcases hh with hp|hfib
        · exact Finset.mem_union_right B ((hP z).mpr ⟨hz.1,hp⟩)
        · let w : UpperHalfPlane := ⟨z,hz.1⟩
          have hza : z∈potentialSuperlevel k (halfPlaneFunction f) ξ a := by
            rw [← squaredReciprocalPotential_sublevel ha]
            exact hz
          have hw : w∈criticalCut k f ξ a := ⟨hfib,
            (criticalHeight_superlevel hk hz.1 (halfPlaneFunction_deriv_ne_zero f hz.1) ha hfib).mp hza⟩
          rw [hcut] at hw
          exact Finset.mem_union_left P (Finset.mem_image.mpr ⟨w,(hT w).mpr hw,rfl⟩)
      · intro hzC
        rcases Finset.mem_union.mp hzC with hb|hp
        · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
          exact Or.inr ((hT w).mp hw).1
        · exact Or.inl ((hP z).mp hp).2
    have hdet : ∀ z∈C, Grid.hessianDet u z≠0 := by
      intro z hz
      have hzH := (interior_subset (hCint z hz)).1
      have hF := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hzH)
      have hd := halfPlaneFunction_deriv_ne_zero f hzH
      rcases Finset.mem_union.mp hz with hb|hp
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
        have hw' := (hT w).mp hw
        rw [squaredReciprocalPotential_hessian_det hk.ne' hzH hF hd hw'.1]
        apply mul_ne_zero _ (hg.2.1 w hw'.1)
        apply neg_ne_zero.mpr
        have hpole : halfPlaneFunction f w≠ξ := fun he=>criticalMap_ne_image hk.ne' w.im_pos hd (hw'.1.trans he.symm)
        have hhU : 0<squaredReciprocalPotential k (halfPlaneFunction f) ξ w := by
          rw [squaredReciprocalPotential_eq_exp w.im_pos hpole]
          exact Real.exp_pos _
        positivity
      · exact (squaredReciprocalPotential_hessian_det_pole hzH hF hd ((hP z).mp hp).2).ne'
    have hneK : (interior K).Nonempty := by
      obtain ⟨z,hz⟩ := hne
      exact ⟨z,hBint z ((hT z).mpr hz.1)⟩
    have hlower := Grid.compact_halfPlane_morse_sum hK hneK C hc hCint hU htr hdet
    have hdisj : Disjoint B P := by
      apply Finset.disjoint_left.mpr
      intro z hz hp
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      have hw' := (hT w).mp hw
      exact criticalMap_ne_image hk.ne' w.im_pos (halfPlaneFunction_deriv_ne_zero f w.im_pos)
        (hw'.1.trans ((hP w).mp hp).2.symm)
    have hsumB : (∑ z∈B,Grid.morseSign u z)=
        ((maximaCut k f ξ h).ncard:ℤ)-(saddleCut k f ξ h).ncard := by
      rw [Finset.sum_image (fun _ _ _ _ he=>UpperHalfPlane.coe_injective he)]
      exact criticalCut_morse_sum hk hg hh
    have hsumP : (∑ z∈P,Grid.morseSign u z)=(P.card:ℤ) := by
      have hs : (∑ z∈P, Grid.morseSign u z)=∑ _z∈P,(1:ℤ) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hp := (hP z).mp hz
        have hd := squaredReciprocalPotential_hessian_det_pole (k:=k) hp.1
          ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hp.1))
          (halfPlaneFunction_deriv_ne_zero f hp.1) hp.2
        exact ite_eq_left hd
      rw [hs]
      simp
    have hPcard : P.card≤1 := Finset.card_le_one.mpr (by
      intro z hz w hw
      exact source_poles_subsingleton f ξ ((hP z).mp hz) ((hP w).mp hw))
    have hPcardZ : (P.card:ℤ)≤1 := by exact_mod_cast hPcard
    change 1≤∑ z∈B∪P,Grid.morseSign u z at hlower
    rw [Finset.sum_union hdisj,hsumB,hsumP] at hlower
    have hhZ : ((saddleCut k f ξ h).ncard:ℤ)≤(maximaCut k f ξ h).ncard := by omega
    exact_mod_cast hhZ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,Set.ncard_empty]
    exact Nat.zero_le _

end
end StrictInverseFirstPower

end

end OAI
