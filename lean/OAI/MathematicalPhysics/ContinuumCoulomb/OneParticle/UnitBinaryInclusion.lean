import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearPromise

namespace OAI

/-! The unit-charge target is a special case of the binary-charge target.
The inclusion preserves the actual full fermionic continuum energy and
both promise thresholds. -/

namespace ContinuumCoulomb

def UnitCoulomb.toBinary (d : UnitCoulomb) : BinaryCoulomb where
  nuclei := d.nuclei.map (fun r => (r, 1))
  electrons := d.electrons
  lower := d.lower
  upper := d.upper

theorem UnitCoulomb.toBinary_valid (d : UnitCoulomb) (h : d.Valid) : d.toBinary.Valid := by
  dsimp only [UnitCoulomb.toBinary]
  refine {
    nuclei_pos := by simpa only [UnitCoulomb.toBinary, List.length_map] using h.nuclei_pos
    electrons_pos := h.electrons_pos
    positions := ?_
    distinct := ?_
    charge_pos := ?_
    lower_denominator := h.lower_denominator
    upper_denominator := h.upper_denominator
    gap := h.gap }
  · intro a
    change ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).1.Valid
    simp only [List.get_eq_getElem, List.getElem_map]
    exact h.positions ⟨a.val, by simpa only [List.length_map] using a.isLt⟩
  · intro a b hab
    change ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).1.value =
      ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get b).1.value at hab
    simp only [List.get_eq_getElem, List.getElem_map] at hab
    have h' := h.distinct (a₁ := ⟨a.val, by simpa only [List.length_map] using a.isLt⟩)
      (a₂ := ⟨b.val, by simpa only [List.length_map] using b.isLt⟩) hab
    exact Fin.ext (congrArg (fun x : Fin d.nuclei.length => x.val) h')
  · intro a
    change 0 < ((d.nuclei.map (fun r => (r, (1 : ℕ)))).get a).2
    simp only [List.get_eq_getElem, List.getElem_map]
    exact Nat.zero_lt_one

private theorem nuclearData_ext (d e : NuclearData) (hn : d.nuclei=e.nuclei)
    (hp : ∀ i, d.position i=e.position (Fin.cast hn i))
    (hz : ∀ i, d.charge i=e.charge (Fin.cast hn i)) (he : d.electrons=e.electrons) : d=e := by
  rcases d with ⟨nd,hnd,pd,hd,zd,hzd,ed,hed⟩
  rcases e with ⟨ne,hne,pe,he',ze,hze,ee,hee⟩
  dsimp only at hn hp hz he
  subst ne
  simp only [Fin.cast_refl, id_eq] at hp hz
  have hp' := funext hp
  have hz' := funext hz
  subst pe
  subst ze
  subst ee
  rfl

theorem UnitCoulomb.toBinary_toData (d : UnitCoulomb) (h : d.Valid) :
    d.toBinary.toData (d.toBinary_valid h) = (d.toData h).toNuclearData := by
  apply nuclearData_ext _ _ (by exact List.length_map (fun r => (r, (1 : ℕ))))
  · intro i
    dsimp only [UnitCoulomb.toBinary, BinaryCoulomb.toData, UnitCoulomb.toData,
      UnitNuclearData.toNuclearData] at i ⊢
    simp only [List.get_eq_getElem, List.getElem_map, Fin.val_cast]
  · intro i
    dsimp only [UnitCoulomb.toBinary, BinaryCoulomb.toData, UnitCoulomb.toData,
      UnitNuclearData.toNuclearData] at i ⊢
    simp only [List.get_eq_getElem, List.getElem_map]
  · rfl

noncomputable section

theorem UnitCoulomb.toBinary_energy (d : UnitCoulomb) (h : d.Valid) :
    groundEnergy (d.toBinary.toData (d.toBinary_valid h)) = unitGroundEnergy (d.toData h) := by
  rw [d.toBinary_toData h, unit_groundEnergy_eq]

theorem unitBinary_yes {d : UnitCoulomb} (h : d ∈ unitCoulombPromise.yes) :
    d.toBinary ∈ binaryCoulombPromise.yes := by
  obtain ⟨hv, he⟩ := h
  refine ⟨d.toBinary_valid hv, ?_⟩
  rw [d.toBinary_energy hv]
  exact he

theorem unitBinary_no {d : UnitCoulomb} (h : d ∈ unitCoulombPromise.no) :
    d.toBinary ∈ binaryCoulombPromise.no := by
  obtain ⟨hv, he⟩ := h
  refine ⟨d.toBinary_valid hv, ?_⟩
  rw [d.toBinary_energy hv]
  exact he

end
end ContinuumCoulomb

end OAI
