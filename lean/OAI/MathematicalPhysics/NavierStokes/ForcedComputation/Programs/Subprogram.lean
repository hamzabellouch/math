import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-! Removing instructions preserves the geometric conditions of a processor.
The fresh-state initializer uses this to remove an unreachable incoming row. -/

namespace ShearFlows

def Input.withInstructions (d : Input) (l : List Instruction) : Input :=
  { d with instructions := l }

theorem ValidInput.withInstructions {d : Input} (hd : ValidInput d)
    {l : List Instruction} (hl : l.Sublist d.instructions) :
    ValidInput (d.withInstructions l) := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hl
  have hmem : ∀ b ∈ l, b ∈ d.instructions := fun _ hb => hl.subset hb
  refine {
    period_pos := hd.period_pos
    chart_positive := hd.chart_positive
    chart_length := hd.chart_length
    h_pos := hd.h_pos
    centers_nonempty := hd.centers_nonempty
    chartMargin := hd.chartMargin
    height_inside := hd.height_inside
    source_positive := fun b hb => hd.source_positive b (hmem b hb)
    target_positive := fun b hb => hd.target_positive b (hmem b hb)
    source_in_chart := fun b hb => hd.source_in_chart b (hmem b hb)
    target_in_chart := fun b hb => hd.target_in_chart b (hmem b hb)
    factor_pos := fun b hb => hd.factor_pos b (hmem b hb)
    image_eq := fun b hb => hd.image_eq b (hmem b hb)
    source_separation := ?_
    target_separation := ?_
    halfWidths := fun b hb => hd.halfWidths b (hmem b hb)
    source_centers := fun b hb => hd.source_centers b (hmem b hb)
    target_centers := fun b hb => hd.target_centers b (hmem b hb) }
  · intro i j hij
    have h := hd.source_separation (f i) (f j) (fun he => hij (f.injective he))
    change PositivelySeparated (d.instructions.get (f i)).source.carrier
      (d.instructions.get (f j)).source.carrier at h
    rw [← hf i, ← hf j] at h
    exact h
  · intro i j hij
    have h := hd.target_separation (f i) (f j) (fun he => hij (f.injective he))
    change PositivelySeparated (d.instructions.get (f i)).target.carrier
      (d.instructions.get (f j)).target.carrier at h
    rw [← hf i, ← hf j] at h
    exact h

def Input.filterInstructions (d : Input) (p : Instruction → Bool) : Input :=
  d.withInstructions (d.instructions.filter p)

theorem ValidInput.filterInstructions {d : Input} (hd : ValidInput d)
    (p : Instruction → Bool) : ValidInput (d.filterInstructions p) :=
  hd.withInstructions List.filter_sublist

theorem PositivelySeparated.symm {A B : Set Plane} (h : PositivelySeparated A B) :
    PositivelySeparated B A := by
  obtain ⟨ε, hε, hb⟩ := h
  exact ⟨ε, hε, fun x hx y hy => by simpa only [norm_sub_rev] using hb y hy x hx⟩

theorem indexed_cons_separation {A : Type*} (a : A) (l : List A) (R : A → A → Prop)
    (hsym : ∀ a b, R a b → R b a)
    (hhead : ∀ b ∈ l, R a b)
    (htail : ∀ i j : Fin l.length, i ≠ j → R l[i] l[j])
    (i j : Fin (a :: l).length) (hij : i ≠ j) : R (a :: l)[i] (a :: l)[j] := by
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact False.elim (hij rfl)
    | succ j => simpa using hhead l[j] (List.getElem_mem j.isLt)
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa using hsym a l[i] (hhead l[i] (List.getElem_mem i.isLt))
    | succ j =>
      exact htail i j (fun he => hij (congrArg Fin.succ he))

theorem ValidInput.consInstruction {d : Input} (hd : ValidInput d) (b : Instruction)
    (hb : ValidInput (d.withInstructions [b]))
    (hs : ∀ c ∈ d.instructions, PositivelySeparated b.source.carrier c.source.carrier)
    (ht : ∀ c ∈ d.instructions, PositivelySeparated b.target.carrier c.target.carrier) :
    ValidInput (d.withInstructions (b :: d.instructions)) := by
  have hall {P : Instruction → Prop} (hp : P b) (hps : ∀ c ∈ d.instructions, P c) :
      ∀ c ∈ b :: d.instructions, P c := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hp
    · exact hps c hc
  refine {
    period_pos := hd.period_pos
    chart_positive := hd.chart_positive
    chart_length := hd.chart_length
    h_pos := hd.h_pos
    centers_nonempty := hd.centers_nonempty
    chartMargin := hd.chartMargin
    height_inside := hd.height_inside
    source_positive := hall (hb.source_positive b (by simp [Input.withInstructions]))
      hd.source_positive
    target_positive := hall (hb.target_positive b (by simp [Input.withInstructions]))
      hd.target_positive
    source_in_chart := hall (hb.source_in_chart b (by simp [Input.withInstructions]))
      hd.source_in_chart
    target_in_chart := hall (hb.target_in_chart b (by simp [Input.withInstructions]))
      hd.target_in_chart
    factor_pos := hall (hb.factor_pos b (by simp [Input.withInstructions])) hd.factor_pos
    image_eq := hall (hb.image_eq b (by simp [Input.withInstructions])) hd.image_eq
    source_separation := indexed_cons_separation b d.instructions
      (fun a c => PositivelySeparated a.source.carrier c.source.carrier)
      (fun _ _ h => h.symm) hs hd.source_separation
    target_separation := indexed_cons_separation b d.instructions
      (fun a c => PositivelySeparated a.target.carrier c.target.carrier)
      (fun _ _ h => h.symm) ht hd.target_separation
    halfWidths := hall (hb.halfWidths b (by simp [Input.withInstructions])) hd.halfWidths
    source_centers := hall (hb.source_centers b (by simp [Input.withInstructions]))
      hd.source_centers
    target_centers := hall (hb.target_centers b (by simp [Input.withInstructions]))
      hd.target_centers }

theorem ValidInput.prependSublist {d : Input} (hd : ValidInput d)
    {l : List Instruction} (hl : l.Sublist d.instructions) (b : Instruction)
    (hb : ValidInput (d.withInstructions [b]))
    (hs : ∀ c ∈ l, PositivelySeparated b.source.carrier c.source.carrier)
    (ht : ∀ c ∈ l, PositivelySeparated b.target.carrier c.target.carrier) :
    ValidInput (d.withInstructions (b :: l)) := by
  have hv := hd.withInstructions hl
  exact hv.consInstruction b hb hs ht

end ShearFlows

end OAI
