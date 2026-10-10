import OAI.ModelTheory.Choiceless.Reachability

namespace OAI

noncomputable section

namespace CPTSeparation.Grid

open Classical Finset Support

variable {n : ℕ}

private theorem four_fibers {α β : Type*} [Fintype α] [DecidableEq β]
    (f₀ f₁ f₂ f₃ : α → β) (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (h₂ : Function.Injective f₂) (h₃ : Function.Injective f₃) (e : β)
    (p : α → Prop) [DecidablePred p] (hp : ∀ a, p a → f₀ a = e ∨ f₁ a = e ∨ f₂ a = e ∨ f₃ a = e) :
    Fintype.card {a // p a} ≤ 4 := by
  have hcard (f : α → β) (hf : Function.Injective f) :
      (univ.filter (fun a => f a = e)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hf ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm)
  rw [Fintype.card_subtype]
  have hs : univ.filter p ⊆
      ((univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e)) ∪
      univ.filter (fun a => f₂ a = e)) ∪ univ.filter (fun a => f₃ a = e) := by
    intro a ha
    have h := hp a (mem_filter.mp ha).2
    simpa only [mem_union,mem_filter,mem_univ,true_and,or_assoc] using h
  exact (card_le_card hs).trans (le_trans (card_union_le _ _) (by
    have h01 := card_union_le (univ.filter (fun a => f₀ a = e)) (univ.filter (fun a => f₁ a = e))
    have h012 := card_union_le
      (univ.filter (fun a => f₀ a = e) ∪ univ.filter (fun a => f₁ a = e))
      (univ.filter (fun a => f₂ a = e))
    have := hcard f₀ h₀; have := hcard f₁ h₁; have := hcard f₂ h₂; have := hcard f₃ h₃
    omega))

theorem edgeFaces_card_le (e : Edge n) : Fintype.card (EdgeFaces e) ≤ 12 := by
  have hxy : Fintype.card {f : FaceXY n // cycle (.inl f) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXY n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j.castSucc k)
      (fun ⟨i,j,k⟩ => ey i.succ j k) (fun ⟨i,j,k⟩ => ex i j.succ k)
      (fun ⟨i,j,k⟩ => ey i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hxz : Fintype.card {f : FaceXZ n // cycle (.inr (.inl f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceXZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ex i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i.succ j k) (fun ⟨i,j,k⟩ => ex i j k.succ)
      (fun ⟨i,j,k⟩ => ez i.castSucc j k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ex] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  have hyz : Fintype.card {f : FaceYZ n // cycle (.inr (.inr f)) e ≠ 0} ≤ 4 := by
    refine four_fibers (α := FaceYZ n) (β := Edge n) (fun ⟨i,j,k⟩ => ey i j k.castSucc)
      (fun ⟨i,j,k⟩ => ez i j.succ k) (fun ⟨i,j,k⟩ => ey i j k.succ)
      (fun ⟨i,j,k⟩ => ez i j.castSucc k) ?_ ?_ ?_ ?_ e _ ?_
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ey] using h
    · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h; simpa [ez] using h
    · rintro ⟨i,j,k⟩ h
      by_contra hn
      push Not at hn
      apply h
      simp [cycle,Pi.single_eq_of_ne,Ne.symm hn.1,Ne.symm hn.2.1,
        Ne.symm hn.2.2.1,Ne.symm hn.2.2.2]
  unfold EdgeFaces Face
  rw [Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum,
    Fintype.card_congr Equiv.subtypeSum,Fintype.card_sum]
  omega

def localSizeBound : ℕ := 3^25

theorem localGroup_card_le (e : Edge n) : Fintype.card (LocalGroup e) ≤ localSizeBound := by
  rw [Fintype.card_congr (Support.H.productEquiv (localCycle e)),Fintype.card_prod,
    Fintype.card_fun,Fintype.card_prod]
  have hf := edgeFaces_card_le e
  simp only [Scalar,ZMod.card] at *
  change (3*3)^Fintype.card (EdgeFaces e)*3 ≤ 3^25
  calc
    (3*3)^Fintype.card (EdgeFaces e)*3 ≤ (3*3)^12*3 :=
      Nat.mul_le_mul_right 3 (Nat.pow_le_pow_right (by norm_num) hf)
    _ = 3^25 := by norm_num

theorem configuration_card_le (b : Vertex n → Scalar) (v : Vertex n) :
    Fintype.card (Configuration b v) ≤ localSizeBound^6 := by
  have hi : Function.Injective (fun s : Configuration b v => s.state) :=
    fun s t h => Configuration.ext (congrFun h)
  have hdegree : Fintype.card (IncidentEdges v) ≤ 6 := degree_le_six v
  calc
    Fintype.card (Configuration b v) ≤ Fintype.card (LocalStates v) := Fintype.card_le_of_injective _ hi
    _ = ∏ e : IncidentEdges v, Fintype.card (LocalGroup e.val) := Fintype.card_pi
    _ ≤ ∏ _e : IncidentEdges v, localSizeBound := Finset.prod_le_prod (fun e _ => localGroup_card_le e.val)
    _ = localSizeBound^Fintype.card (IncidentEdges v) := by simp
    _ ≤ localSizeBound^6 := Nat.pow_le_pow_right (by norm_num [localSizeBound]) hdegree

def atomSizeConstant : ℕ := 3*localSizeBound+localSizeBound^6

theorem atom_card_bounds (hn : 1 ≤ n) (b : Vertex n → Scalar) :
    (n+1)^3 ≤ Fintype.card (Atom b) ∧
    Fintype.card (Atom b) ≤ atomSizeConstant*(n+1)^3 := by
  have hv : Fintype.card (Vertex n) = (n+1)^3 := by simp [Vertex]; ring
  have he : Fintype.card (Edge n) ≤ 3*(n+1)^3 := by
    simp only [Edge,EdgeX,EdgeY,EdgeZ,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    nlinarith
  constructor
  · rw [← hv]
    apply Fintype.card_le_of_injective (fun v : Vertex n => (.inr ⟨v,someConfiguration hn b v⟩ : Atom b))
    intro v w h
    exact congrArg Sigma.fst (Sum.inr.inj h)
  · change Fintype.card ((Σ e : Edge n, LocalGroup e) ⊕ (Σ v : Vertex n, Configuration b v)) ≤ _
    rw [← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_sigma, Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card]
    calc
      (∑ e : Edge n, Fintype.card (LocalGroup e))+
          ∑ v : Vertex n, Fintype.card (Configuration b v) ≤
          (∑ _e : Edge n, localSizeBound)+∑ _v : Vertex n, localSizeBound^6 :=
        add_le_add (sum_le_sum (fun e _ => localGroup_card_le e))
          (sum_le_sum (fun v _ => configuration_card_le b v))
      _ = Fintype.card (Edge n)*localSizeBound+Fintype.card (Vertex n)*localSizeBound^6 := by simp
      _ ≤ (3*(n+1)^3)*localSizeBound+(n+1)^3*localSizeBound^6 := by
        rw [hv]
        exact add_le_add (Nat.mul_le_mul_right _ he) (le_refl _)
      _ = atomSizeConstant*(n+1)^3 := by unfold atomSizeConstant; ring

end CPTSeparation.Grid

namespace CPTSeparation.Hereditary

open Classical

variable {A G : Type*} [Group G] [MulAction G A] {s : ℕ}

theorem hereditary_iff {x : HF A} : HereditarilySupported (G := G) s x ↔
    Supported (G := G) s x ∧ ∀ y, y ∈ x → HereditarilySupported (G := G) s y := by
  constructor
  · intro h
    exact ⟨h x .refl,fun y hy z hz => h z (hz.tail hy)⟩
  · rintro ⟨h,hm⟩ y hy
    cases hy with
    | refl => exact h
    | tail hz hzx => exact hm _ hzx _ hz

theorem hereditary_transitive {x y : HF A} (hx : HereditarilySupported (G := G) s x) (hy : y ∈ x) :
    HereditarilySupported (G := G) s y := (hereditary_iff.mp hx).2 y hy

theorem ordinal_hereditary [Nonempty A] (s j : ℕ) :
    HereditarilySupported (G := G) s (ordinal (A := A) j) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    apply hereditary_iff.mpr
    constructor
    · refine ⟨fun _ => Classical.choice (inferInstance : Nonempty A),?_⟩
      intro g _
      exact map_ordinal (fun a => g • a) j
    · intro y hy
      obtain ⟨k,hk,rfl⟩ := (mem_ordinal y j).mp hy
      exact ih k hk

end CPTSeparation.Hereditary

namespace CPTSeparation.Grid

section

open Classical Hereditary Counting HFCoding Interpretations

variable {n : ℕ} (b : Vertex n → Scalar)

abbrev programInput : Interpretations.Structure Symbol where
  Carrier := Atom b
  finite := inferInstance
  rel := (atomInput b).rel

def programActionIso (g : BoxGroup n) : (programInput b).Iso (programInput b) where
  equiv := (actionIso (b := b) g).toEquiv
  rel r x y := ((actionIso (b := b) g).rel_eq r x y).symm

variable (P : Interpretations.Program Symbol)

theorem trace_supported (hn : 1 ≤ n) (B K N : ℕ) (hB : 2 ≤ B) (hK : K ≤ B)
    (hN : Nat.card (Atom b) ≤ B) (hNpos : 0 < N)
    (hsize : ∀ j < K, Nat.card (P.state (programInput b) j).Carrier ≤ B)
    (q : ℝ) (hq : 0 ≤ q) (hpoly : (9*B^3 : ℝ) ≤ (N : ℝ)^q) :
    ∀ x ∈ P.family (programInput b) B K,
      HereditarilySupported (G := CentralGroup n) ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ x := by
  obtain ⟨hc,ht,hi⟩ := P.trace_family (programInput b) B K hB hK hN hsize
  have hInv : ∀ g : BoxGroup n, ∀ x ∈ P.family (programInput b) B K,
      g • x ∈ P.family (programInput b) B K := by
    intro g x hx
    exact hi (programActionIso b g) x hx
  exact invariant_family_hereditarily_supported hn _ hInv ht N hNpos q hq
    (le_trans (by exact_mod_cast hc) hpoly)

variable {ι : Type} (bs : ι → Vertex n → Scalar) {s m : ℕ}

def programDomain (i : ι) : Set (HF (Atom (bs i))) := HereditarilySupported (G := CentralGroup n) s

def programHF (i : ι) : Counting.Structure (Forms.HFRelation AnalysisSymbol) (Domain (programDomain bs (s := s) i)) :=
  Forms.hfStructure (analysisStructure (bs i))

theorem program_domain_transitive (i : ι) :
    ∀ x ∈ programDomain bs (s := s) i, ∀ y, y ∈ x → y ∈ programDomain bs (s := s) i :=
  fun _ hx _ hy => hereditary_transitive hx hy

theorem program_mem_uniform : UniformDefinable (programHF bs (s := s)) m 2
    (fun _ v => (v 0).val ∈ (v 1).val) :=
  UniformDefinable.relation (S := programHF bs (s := s)) .mem 0 1

theorem program_set_uniform : UniformDefinable (programHF bs (s := s)) m 1
    (fun _ v => isSet (v 0).val = true) := by
  apply (UniformDefinable.relation (S := programHF bs (s := s)) .atom 0 0).neg.congr
  intro i v
  change (¬ isSet (v 0).val = false) ↔ _
  cases isSet (v 0).val <;> simp

theorem program_pure (hn : 1 ≤ n) (i : ι) (k : ℕ) : ordinal k ∈ programDomain bs (s := s) i := by
  let := atom_nonempty hn (bs i)
  exact ordinal_hereditary s k

variable {B K : ℕ}

variable (hfamily : ∀ i x, x ∈ P.family (programInput (bs i)) B K → x ∈ programDomain bs (s := s) i)

theorem program_input_definable : StateDefinable (fun i => programInput (bs i)) (programHF bs)
    (P.inputCode (fun i => programInput (bs i)) hfamily) m := by
  constructor
  · apply (UniformDefinable.relation (S := programHF bs) .atom 0 0).congr
    intro i v
    change isSet (v 0).val = false ↔ ∃ a, _
    constructor
    · intro hx
      rcases atom_or_set (v 0).val with ⟨a,ha⟩|ha
      · exact ⟨a,Subtype.ext ha.symm⟩
      · rw [ha,isSet_ofFinset] at hx
        cases hx
    · rintro ⟨a,ha⟩
      rw [← congrArg Subtype.val ha]
      rfl
  · intro r
    apply (UniformDefinable.relation (S := programHF bs) (.base (.input r)) 0 1).congr
    intro i v
    change (∃ a b, (v 0).val = atom a ∧ (v 1).val = atom b ∧ AtomRelation (bs i) r a b) ↔ _
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    refine and_congr ?_ (and_congr ?_ ?_)
    · exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    · exact ⟨fun h => Subtype.ext h.symm,fun h => (congrArg Subtype.val h).symm⟩
    · simp [atomInput]

end

open Classical Hereditary Counting HFCoding Interpretations

variable {n B K N m M : ℕ} (P : Program Symbol) (vstar : Vertex n)

def twoCharges : Bool → Vertex n → Scalar
  | false => 0
  | true => Pi.single vstar 1

variable (hn : 1 ≤ n) (hB : 2 ≤ B) (hK : K ≤ B) (hNpos : 0 < N)

variable (hN : ∀ i, Nat.card (Atom (twoCharges vstar i)) ≤ B)

variable (hsize : ∀ i j, j < K → Nat.card (P.state (programInput (twoCharges vstar i)) j).Carrier ≤ B)

variable (q : ℝ) (hq : 0 ≤ q) (hpoly : (9*B^3 : ℝ) ≤ (N : ℝ)^q)

variable (hm : 6 ≤ m)

variable (wiδ : P.init.domain.scopedWidth < m) (wiη : P.init.identify.scopedWidth < m)

variable (wiρ : ∀ r, (P.init.relation r).scopedWidth < m)

variable (wsδ : P.step.domain.scopedWidth < m) (wsη : P.step.identify.scopedWidth < m)

variable (wsρ : ∀ r, (P.step.relation r).scopedWidth < m)

include hn hB hK hNpos hN hsize hq hpoly hm wiδ wiη wiρ wsδ wsη wsρ

theorem stage_sentence_agrees
    (hs : 0 < ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊)
    (hwidth : max 4 (m+1)*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊ ≤ M)
    (hhom : (7*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)+
      7*((6*(max 2 m*⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊):ℝ)/boxConstant)^((3:ℝ)/2)+1 ≤ M)
    (hgiant : GiantBound n M)
    {j : ℕ} (hj : j < K) (ψ : Interpretations.Formula P.StateSymbols 0) (hw : ψ.scopedWidth < m) :
    ψ.holds (P.state (programInput (0 : Vertex n → Scalar)) j) ↔
      ψ.holds (P.state (programInput (Pi.single vstar 1)) j) := by
  let s := ⌈2*(n+1:ℝ)*(q*Real.logb 3 N)^2⌉₊
  let S := fun i => programInput (twoCharges vstar i)
  let C := programHF (twoCharges vstar) (s := s)
  have hfamily : ∀ i x, x ∈ P.family (S i) B K → x ∈ programDomain (twoCharges vstar) (s := s) i :=
    fun i => trace_supported (twoCharges vstar i) P hn B K N hB hK (hN i) hNpos
      (hsize i) q hq hpoly
  have hd := P.state_definable S C hfamily (program_domain_transitive (twoCharges vstar))
    (program_mem_uniform (twoCharges vstar)) (program_set_uniform (twoCharges vstar)) hm
    (program_pure (twoCharges vstar) hn) hN hsize wiδ wiη wiρ wsδ wsη wsρ
    (program_input_definable P (twoCharges vstar) hfamily) hj
  obtain ⟨φ,hφ,hφψ⟩ := hd.sentence (fun i => P.state (S i) j) C (P.stateCode S hfamily hj)
    (P.stateCode_injective S hfamily hj) (fun i => hsize i j hj) ψ hw
  let v : Fin m → Domain (programDomain (twoCharges vstar) (s := s) false) :=
    fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn false 0⟩
  let w : Fin m → Domain (programDomain (twoCharges vstar) (s := s) true) :=
    fun _ => ⟨ordinal 0,program_pure (twoCharges vstar) hn true 0⟩
  let := atom_nonempty hn (0 : Vertex n → Scalar)
  let := atom_nonempty hn (Pi.single vstar 1)
  exact (hφψ false v).symm.trans ((grid_hf_transfer hn hs (by omega) vstar
    hwidth hhom hgiant φ hφ v w).trans (hφψ true w))

end CPTSeparation.Grid

namespace CPTSeparation.Quantitative

section

open Filter Asymptotics Topology

lemma const_little_rpow (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun _ : ℝ => c) =o[atTop] (fun L => L^r) :=
  (isLittleO_const_id_atTop c).comp_tendsto (tendsto_rpow_atTop hr)

lemma power_little_power {a b : ℝ} (hab : a < b) :
    (fun L : ℝ => L^a) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^a) atTop).mul_isLittleO (const_little_rpow 1 (sub_pos.mpr hab))
  apply h.congr' (by filter_upwards [] with L; simp)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_add hL]
  congr 1
  ring

lemma ceil_little {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (h : f =o[l] g) (h1 : (fun _ => (1:ℝ)) =o[l] g) :
    (fun x => (⌈f x⌉₊ : ℝ)) =o[l] g := by
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hf,h.bound (show 0 < c/2 by linarith),h1.bound (show 0 < c/2 by linarith)] with x hx hh hconst
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [Real.norm_of_nonneg hx] at hh
  norm_num at hconst
  have hb := Nat.ceil_lt_add_one hx
  simp only [Real.norm_eq_abs] at hh ⊢
  linarith

def radius (C q L : ℝ) : ℕ := ⌈2*L*(q*Real.logb 3 (C*L^3))^2⌉₊

def palette (L : ℝ) : ℕ := ⌊L^((7:ℝ)/4)⌋₊

lemma log_volume_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => q*Real.logb 3 (C*L^3)) =o[atTop] (fun L => L^((1:ℝ)/12)) := by
  have hc := const_little_rpow (Real.log C) (show 0 < (1:ℝ)/12 by norm_num)
  have hl := (isLittleO_log_rpow_atTop (show 0 < (1:ℝ)/12 by norm_num)).const_mul_left 3
  have h := ((hc.add hl).const_mul_left ((q:ℝ)/Real.log 3))
  apply h.congr' _ (Filter.Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  simp only [Real.logb,Real.log_mul (ne_of_gt hC) (ne_of_gt (pow_pos hL 3)),Real.log_pow]
  ring

lemma radius_little (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
  have hlog := log_volume_little C q hC
  have hsquare := hlog.pow (show 0 < 2 by omega)
  have hlin := (isBigO_refl (fun L : ℝ => L) atTop).mul_isLittleO hsquare
  have hraw : (fun L : ℝ => 2*L*(q*Real.logb 3 (C*L^3))^2) =o[atTop] (fun L => L^((7:ℝ)/6)) := by
    apply (hlin.const_mul_left 2).congr' (by filter_upwards [] with L; ring)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
    calc
      L * (L ^ ((1:ℝ)/12)) ^ 2 = L^((1:ℝ)) * L^(((1:ℝ)/12)*2) := by
        rw [Real.rpow_one, Real.rpow_mul hL.le]; norm_num
      _ = L^((7:ℝ)/6) := by rw [← Real.rpow_add hL]; norm_num
  apply ceil_little _ hraw (const_little_rpow 1 (by norm_num))
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  positivity

lemma radius_little_palette (C q : ℝ) (hC : 0 < C) :
    (fun L : ℝ => (radius C q L : ℝ)) =o[atTop] (fun L => L^((7:ℝ)/4)) :=
  (radius_little C q hC).trans (power_little_power (by norm_num))

lemma homogeneity_little (C q m c : ℝ) (hC : 0 < C) :
    (fun L : ℝ => 7*(m*(radius C q L:ℝ))+7*((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1)
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
  have hlin := (radius_little_palette C q hC).const_mul_left (7*m)
  have hsr := (radius_little C q hC).const_mul_left (6*m/c)
  have hp := hsr.rpow (show 0 < (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((6*(m*(radius C q L:ℝ)))/c)^((3:ℝ)/2))
      =o[atTop] (fun L => L^((7:ℝ)/4)) := by
    apply hp.congr' (by filter_upwards [] with L; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := (hlin.add (hp'.const_mul_left 7)).add (const_little_rpow 1 (by norm_num))
  apply h.congr_left
  intro L
  ring

lemma floor_big (a : ℝ) : (fun L : ℝ => (⌊L^a⌋₊:ℝ)) =O[atTop] (fun L => L^a) := by
  apply IsBigO.of_norm_eventuallyLE
  filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact Nat.floor_le (Real.rpow_nonneg hL _)

lemma giant_little (c : ℝ) :
    (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =o[atTop] (fun L => L^3) := by
  have hb := (floor_big ((7:ℝ)/4)).const_mul_left (12/c)
  have hp := hb.rpow (show 0 ≤ (3:ℝ)/2 by norm_num)
    ((eventually_ge_atTop (0:ℝ)).mono (fun L hL => Real.rpow_nonneg hL _))
  have hp' : (fun L : ℝ => ((12*(palette L:ℝ))/c)^((3:ℝ)/2)) =O[atTop]
      (fun L => L^((21:ℝ)/8)) := by
    apply hp.congr' (by filter_upwards [] with L; simp only [palette]; congr 1; ring)
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    rw [← Real.rpow_mul hL]
    congr 1
    norm_num
  have h := hp'.trans_isLittleO (power_little_power (a := (21:ℝ)/8) (b := 3) (by norm_num))
  exact h.congr_right (fun L => Real.rpow_natCast L 3)

theorem eventual_bounds (C q c : ℝ) (hC : 0 < C) (hc : 0 < c) (m : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      (max 4 (m+1):ℝ)*(radius C q L:ℝ) ≤ (palette L:ℝ) ∧
      7*((max 2 m:ℝ)*(radius C q L:ℝ))+
        7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 ≤ (palette L:ℝ) ∧
      ((12*(palette L:ℝ))/c)^((3:ℝ)/2) < L^3 := by
  have hw := ((radius_little_palette C q hC).const_mul_left (max 4 (m+1):ℝ)).bound
    (show 0 < (1:ℝ)/2 by norm_num)
  have hh := (homogeneity_little C q (max 2 m:ℝ) c hC).bound (show 0 < (1:ℝ)/2 by norm_num)
  have hg := (giant_little c).bound (show 0 < (1:ℝ)/2 by norm_num)
  filter_upwards [hw,hh,hg,eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (show 0 < (7:ℝ)/4 by norm_num)).eventually_ge_atTop 2] with L hw hh hg hL hpow
  have hp : 0 ≤ L^((7:ℝ)/4) := Real.rpow_nonneg hL.le _
  have hs : 0 ≤ (radius C q L:ℝ) := Nat.cast_nonneg _
  have hfl := Nat.lt_floor_add_one (L^((7:ℝ)/4))
  have hn : 0 ≤ 7*((max 2 m:ℝ)*(radius C q L:ℝ))+
      7*((6*((max 2 m:ℝ)*(radius C q L:ℝ)))/c)^((3:ℝ)/2)+1 := by positivity
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hp] at hw
  rw [Real.norm_of_nonneg hn,Real.norm_of_nonneg hp] at hh
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (pow_nonneg hL.le 3)] at hg
  change _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _ ≤ (⌊L^((7:ℝ)/4)⌋₊:ℝ) ∧ _
  refine ⟨by linarith,by linarith,?_⟩
  have hcube := pow_pos hL 3
  linarith

end

def timeExponent (c d : ℕ) := c + 2*d + 2

def traceExponent (c d : ℕ) := 3*timeExponent c d + 4

lemma timeExponent_ge_two (c d : ℕ) : 2 ≤ timeExponent c d := by unfold timeExponent; omega

lemma nat_le_power (N c : ℕ) (hN : 2 ≤ N) : c ≤ N^c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [pow_succ]
    have hp : 1 ≤ N^c := Nat.one_le_pow _ _ (by omega)
    nlinarith

lemma polynomial_bounds (c d N : ℕ) (hN : 2 ≤ N) :
    2 ≤ N^timeExponent c d ∧ N ≤ N^timeExponent c d ∧
    c*(N+1)^d ≤ N^timeExponent c d ∧
    9*(N^timeExponent c d)^3 ≤ N^traceExponent c d := by
  have hpos : 1 ≤ N := by omega
  have hD := timeExponent_ge_two c d
  have hNB : N ≤ N^timeExponent c d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hpos (show 1 ≤ timeExponent c d by omega)
  refine ⟨le_trans hN hNB,hNB,?_,?_⟩
  · calc
      c*(N+1)^d ≤ N^c*(N^2)^d := Nat.mul_le_mul (nat_le_power N c hN)
        (Nat.pow_le_pow_left (by nlinarith : N+1 ≤ N^2) d)
      _ = N^(c+2*d) := by rw [← pow_mul,← pow_add]
      _ ≤ N^timeExponent c d := Nat.pow_le_pow_right hpos (by unfold timeExponent; omega)
  · calc
      9*(N^timeExponent c d)^3 ≤ N^4*(N^timeExponent c d)^3 := by
        apply Nat.mul_le_mul_right
        have hh := Nat.pow_le_pow_left hN 4
        norm_num at hh
        omega
      _ = N^traceExponent c d := by
        rw [← pow_mul,← pow_add]
        unfold traceExponent
        congr 1
        omega

lemma real_trace_bound (c d N : ℕ) (hN : 2 ≤ N) :
    (9*(N^timeExponent c d)^3 : ℝ) ≤ (N:ℝ)^(traceExponent c d:ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast (polynomial_bounds c d N hN).2.2.2

end CPTSeparation.Quantitative

namespace CPTSeparation.Interpretations.Program

open Classical Finset

variable {R : Type} (P : Program R)

lemma stage_le_cost (A : Structure R) (j : ℕ) : j+1 ≤ P.cost A j := by
  unfold cost
  omega

lemma size_le_cost (A : Structure R) {j k : ℕ} (hk : k ≤ j) :
    Nat.card (P.state A k).Carrier ≤ P.cost A j := by
  rw [Nat.card_eq_fintype_card]
  unfold cost
  have h := Finset.single_le_sum (f := fun l => Fintype.card (P.state A l).Carrier)
    (fun l _ => Nat.zero_le _) (show k ∈ Finset.range (j+1) by simpa using hk)
  omega

end CPTSeparation.Interpretations.Program

namespace CPTSeparation.Grid

open Classical Hereditary Counting HFCoding Interpretations Quantitative Filter

lemma atomSizeConstant_pos : 0 < atomSizeConstant := by
  unfold atomSizeConstant localSizeBound
  positivity

theorem exists_numeric_box (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∃ n : ℕ, 1 ≤ n ∧
      let N : ℕ := atomSizeConstant*(n+1)^3
      let s : ℕ := ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊
      let M : ℕ := palette (n+1:ℝ)
      2 ≤ N ∧ 0 < s ∧ max 4 (m+1)*s ≤ M ∧
      (7:ℝ)*((max 2 m*s:ℕ):ℝ)+7*((6*((max 2 m*s:ℕ):ℝ))/boxConstant)^((3:ℝ)/2)+1 ≤ M ∧
      GiantBound n M := by
  have hC : 0 < (atomSizeConstant:ℝ) := by exact_mod_cast atomSizeConstant_pos
  have hev := eventual_bounds (atomSizeConstant:ℝ) (q:ℝ) boxConstant hC boxConstant_pos m
  have ht : Filter.Tendsto (fun n : ℕ => (n+1:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have he := ht.eventually hev
  obtain ⟨n,hn,hnum⟩ := ((eventually_ge_atTop (1:ℕ)).and he).exists
  refine ⟨n,hn,?_⟩
  dsimp only
  let N : ℕ := atomSizeConstant*(n+1)^3
  have hN : 2 ≤ N := by
    have hC' : 1 ≤ atomSizeConstant := atomSizeConstant_pos
    have hp : 2 ≤ (n+1)^3 := by
      have h := Nat.pow_le_pow_left (show 2 ≤ n+1 by omega) 3
      norm_num at h
      omega
    exact hp.trans (by simpa only [one_mul] using Nat.mul_le_mul_right ((n+1)^3) hC')
  have hlog : 0 < Real.logb 3 (N:ℝ) := Real.logb_pos (by norm_num) (by exact_mod_cast hN)
  have hs : 0 < ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    apply Nat.ceil_pos.mpr
    have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
    positivity
  have hrad : radius (atomSizeConstant:ℝ) (q:ℝ) (n+1:ℝ) =
      ⌈2*(n+1:ℝ)*((q:ℝ)*Real.logb 3 N)^2⌉₊ := by
    simp only [radius,N,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  rw [hrad] at hnum
  refine ⟨hN,hs,?_,?_,?_⟩
  · exact_mod_cast hnum.1
  · simpa only [N,Nat.cast_mul, Nat.cast_max, Nat.cast_ofNat] using hnum.2.1
  · simpa only [GiantBound,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using hnum.2.2

end CPTSeparation.Grid

namespace CPTSeparation

def structureQuery (A : Interpretations.Structure Symbol) : Prop :=
  Input.query ({ rel := A.rel } : Input A.Carrier)

namespace Grid

open Classical Hereditary Counting HFCoding Interpretations Quantitative

theorem program_agrees_on_some_box (P : Program Symbol) (hP : P.polynomiallyBounded) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (vstar : Vertex n),
      P.accepts (programInput (0 : Vertex n → Scalar)) ↔
        P.accepts (programInput (Pi.single vstar 1)) := by
  obtain ⟨c,d,hcost⟩ := hP
  obtain ⟨m,hm,wiδ,wiη,wiρ,wsδ,wsη,wsρ,wh,wo⟩ := P.exists_width
  let q := traceExponent c d
  have hq : 0 < q := by dsimp [q,traceExponent]; omega
  obtain ⟨n,hn,hnum⟩ := exists_numeric_box q hq m
  let N := atomSizeConstant*(n+1)^3
  let B := N^timeExponent c d
  let vstar : Vertex n := ⟨0,0,0⟩
  let S := fun i => programInput (twoCharges vstar i)
  have hN : 2 ≤ N := hnum.1
  have hB : 2 ≤ B := (polynomial_bounds c d N hN).1
  have hinput : ∀ i, Fintype.card (S i).Carrier ≤ N :=
    fun i => (atom_card_bounds hn (twoCharges vstar i)).2
  have hbInput : ∀ i, Nat.card (Atom (twoCharges vstar i)) ≤ B := by
    intro i
    apply le_trans _ (polynomial_bounds c d N hN).2.1
    simpa only [Nat.card_eq_fintype_card] using hinput i
  have hcostB (i : Bool) : ∃ j, P.haltsAt (S i) j ∧ P.cost (S i) j ≤ B := by
    obtain ⟨j,hj,hc⟩ := hcost (S i)
    refine ⟨j,hj,hc.trans ?_⟩
    calc
      c*(Fintype.card (S i).Carrier+1)^d ≤ c*(N+1)^d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hinput i) 1) d)
      _ ≤ B := (polynomial_bounds c d N hN).2.2.1
  obtain ⟨j,hj,hjc⟩ := hcostB false
  obtain ⟨k,hk,hkc⟩ := hcostB true
  let K := min j k+1
  have hK : K ≤ B := (by omega : K ≤ j+1).trans ((P.stage_le_cost (S false) j).trans hjc)
  have hsize : ∀ i l, l < K → Nat.card (P.state (programInput (twoCharges vstar i)) l).Carrier ≤ B := by
    intro i l hl
    cases i
    · exact (P.size_le_cost (S false) (by omega : l ≤ j)).trans hjc
    · exact (P.size_le_cost (S true) (by omega : l ≤ k)).trans hkc
  have hpoly : (9*B^3:ℝ) ≤ (N:ℝ)^(q:ℝ) := by
    simpa only [B,q,Nat.cast_pow] using real_trace_bound c d N hN
  have hagree (l : ℕ) (hl : l ≤ min j k) (ψ : Interpretations.Formula P.StateSymbols 0)
      (hw : ψ.scopedWidth < m) :
      ψ.holds (P.state (S false) l) ↔ ψ.holds (P.state (S true) l) := by
    exact stage_sentence_agrees (N := N) P vstar hn hB hK (by omega) hbInput hsize (q:ℝ)
      (by positivity) hpoly hm wiδ wiη wiρ wsδ wsη wsρ
      hnum.2.1 hnum.2.2.1 (by simpa only [N,Nat.cast_mul] using hnum.2.2.2.1) hnum.2.2.2.2 (by omega : l < K) ψ hw
  exact ⟨n,hn,vstar,(P.synchronize (S false) (S true) hj hk
    (fun l hl => hagree l hl P.halt wh) (fun l hl => hagree l hl P.output wo)).2⟩

end Grid

theorem query_not_interpretation_definable :
    Interpretations.NondefinableByInterpretations structureQuery := by
  rintro ⟨P,hpoly,hdecides⟩
  obtain ⟨n,hn,vstar,hagree⟩ := Grid.program_agrees_on_some_box P hpoly
  obtain ⟨hzero,hunit⟩ := Grid.opposite_answers hn vstar
  apply hunit
  exact (hdecides _).mp (hagree.mp ((hdecides _).mpr hzero))

end CPTSeparation

end

end OAI
