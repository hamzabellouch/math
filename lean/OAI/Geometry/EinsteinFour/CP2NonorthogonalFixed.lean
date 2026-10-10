import OAI.Geometry.EinsteinFour.CP2UnitGeometry

namespace OAI

/-! An involution preserving projective transition probabilities fixes the
central line of any nonorthogonal two-point orbit. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

theorem cp2_nonorthogonal_fixed (f : ComplexProjective2 → ComplexProjective2)
    (hinv : Function.Involutive f)
    (hpres : ∀ p q, cp2Overlap (f p) (f q) = cp2Overlap p q)
    (p : ComplexProjective2) (hpos : 0 < cp2Overlap p (f p)) :
    ∃ u, f u = u := by
  by_cases heq : cp2Overlap p (f p) = 1
  · exact ⟨p, ((cp2Overlap_eq_one_iff p (f p)).mp heq).symm⟩
  have hlt : cp2Overlap p (f p) < 1 := lt_of_le_of_ne (cp2Overlap_le_one _ _) heq
  obtain ⟨q, hq0, hqn, hqm, hpq⟩ := cp2_unit_aligned p (f p) hpos
  let c := cp2Overlap p (f p)
  let v := cp2UnitRep p
  have hvn : ‖v‖ = 1 := cp2UnitRep_norm p
  have hv0 : v ≠ 0 := cp2UnitRep_ne_zero p
  obtain ⟨u, hun, htopu⟩ := cp2_aligned_center v q c hvn hqn hpq hpos
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hun; exact zero_ne_one hun
  let U : ComplexProjective2 := Projectivization.mk ℂ u hu0
  let w := cp2UnitRep (f U)
  have hwn : ‖w‖ = 1 := cp2UnitRep_norm (f U)
  have hw0 : w ≠ 0 := cp2UnitRep_ne_zero (f U)
  have hpU : cp2Overlap p U = ‖inner ℂ v u‖ :=
    cp2Overlap_of_unit_representatives p U v u hv0 hu0 hvn hun
      (cp2UnitRep_mk p) rfl
  have hqU : cp2Overlap (f p) U = ‖inner ℂ q u‖ :=
    cp2Overlap_of_unit_representatives (f p) U q u hq0 hu0 hqn hun hqm rfl
  have hpfU : cp2Overlap p (f U) = ‖inner ℂ v w‖ :=
    cp2Overlap_of_unit_representatives p (f U) v w hv0 hw0 hvn hwn
      (cp2UnitRep_mk p) (cp2UnitRep_mk (f U))
  have hqfU : cp2Overlap (f p) (f U) = ‖inner ℂ q w‖ :=
    cp2Overlap_of_unit_representatives (f p) (f U) q w hq0 hw0 hqn hwn
      hqm (cp2UnitRep_mk (f U))
  have hswap : cp2Overlap p (f U) = cp2Overlap (f p) U := by
    simpa only [hinv p] using hpres (f p) U
  have htopw : ‖inner ℂ v w‖ ^ 2 + ‖inner ℂ q w‖ ^ 2 = 1 + c := by
    rw [← hpfU, ← hqfU, hswap, hpres, hpU, hqU]
    simpa only [add_comm] using htopu
  obtain ⟨a, _, ha⟩ := cp2_aligned_pair_top_unique v q u c hvn hqn hun hpq hpos hlt htopu
  obtain ⟨b, _, hb⟩ := cp2_aligned_pair_top_unique v q w c hvn hqn hwn hpq hpos hlt htopw
  have hs : v + q ≠ 0 := by
    intro hs
    rw [hs, smul_zero] at ha
    exact hu0 ha
  refine ⟨U, ?_⟩
  calc
    f U = Projectivization.mk ℂ w hw0 := (cp2UnitRep_mk (f U)).symm
    _ = Projectivization.mk ℂ (v + q) hs :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨b, hb.symm⟩
    _ = Projectivization.mk ℂ u hu0 :=
      ((Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨a, ha.symm⟩).symm
    _ = U := rfl

end
end PositiveEinsteinFour

end OAI
