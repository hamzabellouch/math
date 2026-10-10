import OAI.ModelTheory.Categoricity.Diagrams

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace EndHomogeneous

variable {J X C : Type u} [LinearOrder J] [LinearOrder X]
  (wJ : WellFounded ((· < ·) : J → J → Prop))
  (wX : WellFounded ((· < ·) : X → X → Prop)) (c : Finset X → C)

def residual (x : X) (α : J) (f : ∀ β, β < α → X) : Set X :=
  {y | (∀ β h, f β h < y) ∧
    ∀ a : Finset {β : J // β < α},
      c (insert y (a.image (fun β => f β.val β.property))) =
        c (insert x (a.image (fun β => f β.val β.property)))}

def step (x : X) (α : J) (f : ∀ β, β < α → X) : X := by
  classical
  exact if h : (residual c x α f).Nonempty then wX.min (residual c x α f) h else x

def rep (x : X) : J → X := wJ.fix (step wX c x)

theorem rep_eq (x : X) (α : J) :
    rep wJ wX c x α = step wX c x α (fun β _ => rep wJ wX c x β) :=
  wJ.fix_eq _ α

theorem active (x : X) (α : J) (h : ∀ β < α, rep wJ wX c x β < x) :
    (∀ β < α, rep wJ wX c x β < rep wJ wX c x α) ∧
    (∀ a : Finset {β : J // β < α},
      c (insert (rep wJ wX c x α) (a.image (fun β => rep wJ wX c x β.val))) =
        c (insert x (a.image (fun β => rep wJ wX c x β.val)))) ∧
    rep wJ wX c x α ≤ x := by
  let R := residual c x α (fun β _ => rep wJ wX c x β)
  have hx : x ∈ R := ⟨h, fun _ => rfl⟩
  have hn : R.Nonempty := ⟨x, hx⟩
  have he : rep wJ wX c x α = wX.min R hn := by
    rw [rep_eq, step, dite_eq_left hn]
  rw [he]
  exact ⟨(wX.min_mem R hn).1, (wX.min_mem R hn).2, not_lt.mp (wX.not_lt_min R hx)⟩

theorem lt_of_no_stop (x : X) (α : J)
    (h : ∀ β ≤ α, rep wJ wX c x β ≠ x) : rep wJ wX c x α < x := by
  induction α using wJ.induction with
  | h α ih =>
    have hp : ∀ β < α, rep wJ wX c x β < x := by
      intro β hβ
      exact ih β hβ (fun γ hγ => h γ (hγ.trans hβ.le))
    exact lt_of_le_of_ne (active wJ wX c x α hp).2.2 (h α le_rfl)

def Stops (x : X) : Prop := ∃ α, rep wJ wX c x α = x

def first (x : X) (h : Stops wJ wX c x) : J :=
  wJ.min {α | rep wJ wX c x α = x} h

theorem first_eq (x : X) (h : Stops wJ wX c x) :
    rep wJ wX c x (first wJ wX c x h) = x := wJ.min_mem _ h

theorem before_first (x : X) (h : Stops wJ wX c x) (β : J)
    (hβ : β < first wJ wX c x h) : rep wJ wX c x β < x := by
  apply lt_of_no_stop wJ wX c
  intro γ hγ he
  exact (wJ.not_lt_min _ he) (hγ.trans_lt hβ)

def profile (x : X) (a : Finset J) : C := c (insert x (a.image (rep wJ wX c x)))

theorem equal_reps {x y : X} (α : J)
    (hx : ∀ β < α, rep wJ wX c x β < x)
    (hy : ∀ β < α, rep wJ wX c y β < y)
    (hp : profile wJ wX c x = profile wJ wX c y) :
    rep wJ wX c x α = rep wJ wX c y α := by
  induction α using wJ.induction with
  | h α ih =>
    have hr : ∀ β < α, rep wJ wX c x β = rep wJ wX c y β := by
      intro β hβ
      exact ih β hβ (fun γ hγ => hx γ (hγ.trans hβ))
        (fun γ hγ => hy γ (hγ.trans hβ))
    have hfun : (fun β (_ : β < α) => rep wJ wX c x β) =
        (fun β (_ : β < α) => rep wJ wX c y β) := by funext β hβ; exact hr β hβ
    have hR : residual c x α (fun β _ => rep wJ wX c x β) =
        residual c y α (fun β _ => rep wJ wX c y β) := by
      ext z
      change ((∀ β < α, rep wJ wX c x β < z) ∧ _) ↔
        ((∀ β < α, rep wJ wX c y β < z) ∧ _)
      have hcol (a : Finset {β : J // β < α}) :
          c (insert x (a.image (fun β => rep wJ wX c x β.val))) =
            c (insert y (a.image (fun β => rep wJ wX c y β.val))) := by
        have hh := congrFun hp (a.image Subtype.val)
        simpa only [profile, Finset.image_image, Function.comp_def] using hh
      have hf : (fun β : {β : J // β < α} => rep wJ wX c x β.val) =
          (fun β : {β : J // β < α} => rep wJ wX c y β.val) := by
        funext β; exact hr β.val β.property
      constructor
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun β hβ => by rw [← hr β hβ]; exact h₁ β hβ, ?_⟩
        intro a
        calc
          _ = c (insert z (a.image (fun β => rep wJ wX c x β.val))) := by rw [hf]
          _ = c (insert x (a.image (fun β => rep wJ wX c x β.val))) := h₂ a
          _ = _ := hcol a
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun β hβ => by rw [hr β hβ]; exact h₁ β hβ, ?_⟩
        intro a
        calc
          _ = c (insert z (a.image (fun β => rep wJ wX c y β.val))) := by rw [hf]
          _ = c (insert y (a.image (fun β => rep wJ wX c y β.val))) := h₂ a
          _ = _ := (hcol a).symm
    have hn : (residual c x α (fun β _ => rep wJ wX c x β)).Nonempty :=
      ⟨x, hx, fun _ => rfl⟩
    rw [rep_eq, rep_eq, step, step, dite_eq_left hn, dite_eq_left (hR ▸ hn)]
    congr 1

def stopCode (x : {x : X // Stops wJ wX c x}) : J × (Finset J → C) :=
  (first wJ wX c x.val x.property, profile wJ wX c x.val)

theorem stopCode_injective : Function.Injective (stopCode wJ wX c) := by
  intro x y h
  have hα := congrArg Prod.fst h
  have hp := congrArg Prod.snd h
  apply Subtype.ext
  rw [← first_eq wJ wX c x.val x.property, ← first_eq wJ wX c y.val y.property]
  change first wJ wX c x.val x.property = first wJ wX c y.val y.property at hα
  rw [← hα]
  exact equal_reps wJ wX c _ (before_first wJ wX c x.val x.property)
    (fun β hβ => before_first wJ wX c y.val y.property β (hα ▸ hβ)) hp

include wJ wX in

theorem exists_sequence
    (hcard : #(J × (Finset J → C)) < #X) :
    ∃ x : X, ∃ r : J ↪o X,
      (∀ α, r α < x) ∧
      ∀ α (a : Finset {β : J // β < α}),
        c (insert (r α) (a.image (fun β => r β.val))) =
          c (insert x (a.image (fun β => r β.val))) := by
  have hn : ∃ x : X, ¬ Stops wJ wX c x := by
    by_contra! hall
    let e : X ↪ {x : X // Stops wJ wX c x} :=
      ⟨fun x => ⟨x, hall x⟩, fun _ _ h => congrArg Subtype.val h⟩
    exact hcard.not_ge (Cardinal.mk_le_of_injective
      ((stopCode_injective wJ wX c).comp e.injective))
  obtain ⟨x, hx⟩ := hn
  have hl : ∀ α, rep wJ wX c x α < x := by
    intro α
    exact lt_of_no_stop wJ wX c x α (fun β _ he => hx ⟨β, he⟩)
  have hs : StrictMono (rep wJ wX c x) := by
    intro α β hαβ
    exact (active wJ wX c x β (fun γ _ => hl γ)).1 α hαβ
  refine ⟨x, OrderEmbedding.ofStrictMono _ hs, hl, ?_⟩
  intro α a
  exact (active wJ wX c x α (fun β _ => hl β)).2.1 a

end EndHomogeneous

namespace FinitePartition

def Constant {X C : Type u} (c : Finset X → C) (m : ℕ) (Y : Set X) (p : C) : Prop :=
  ∀ s : Finset X, (↑s : Set X) ⊆ Y → s.card = m → c s = p

def Homogeneous {X C : Type u} (c : Finset X → C) (m : ℕ) (Y : Set X) : Prop :=
  ∃ p, Constant c m Y p

theorem arity_step {J X C : Type u} [LinearOrder J] [LinearOrder X]
    (c : Finset X → C) (x : X) (r : J ↪o X)
    (he : ∀ α (a : Finset {β : J // β < α}),
      c (insert (r α) (a.image (fun β => r β.val))) =
        c (insert x (a.image (fun β => r β.val))))
    {m : ℕ} {Y : Set J}
    (hh : Homogeneous (fun a => c (insert x (a.image r))) m Y) :
    Homogeneous c (m + 1) (r '' Y) := by
  classical
  obtain ⟨p, hp⟩ := hh
  refine ⟨p, ?_⟩
  intro s hs hc
  let t := s.preimage r r.injective.injOn
  have ht : t.image r = s := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.2 (fun a ha => Set.image_subset_range r Y (hs ha))
  have htc : t.card = m + 1 := by
    rw [← Finset.card_image_of_injective t r.injective, ht, hc]
  have htn : t.Nonempty := Finset.card_pos.1 (by omega)
  let α := t.max' htn
  have hα : α ∈ t := Finset.max'_mem t htn
  have hlt : ∀ β ∈ t.erase α, β < α := by
    intro β hβ
    exact lt_of_le_of_ne (Finset.le_max' t β (Finset.mem_erase.1 hβ).2)
      (Finset.mem_erase.1 hβ).1
  let a : Finset {β : J // β < α} :=
    (t.erase α).attach.image (fun β => ⟨β.val, hlt β.val β.property⟩)
  have him : a.image (fun β => r β.val) = (t.erase α).image r := by
    dsimp [a]
    rw [Finset.image_image]
    change (t.erase α).attach.image (r ∘ Subtype.val) = _
    rw [← Finset.image_image, Finset.attach_image_val]
  have hp' : c (insert x ((t.erase α).image r)) = p := by
    apply hp
    · intro β hβ
      have hb : r β ∈ s := Finset.mem_preimage.1 (Finset.mem_erase.1 hβ).2
      obtain ⟨γ, hγ, heq⟩ := hs hb
      exact (r.injective heq) ▸ hγ
    · rw [Finset.card_erase_of_mem hα, htc, Nat.add_sub_cancel]
  calc
    c s = c (insert (r α) ((t.erase α).image r)) := by
      rw [← Finset.image_insert, Finset.insert_erase hα, ht]
    _ = c (insert x ((t.erase α).image r)) := by simpa only [him] using he α a
    _ = p := hp'

theorem power_lt {Λ ξ ζ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hinf : ℵ₀ ≤ Λ) (hξ : ξ < Λ) (hζ : ζ < Λ) : ξ ^ ζ < Λ := by
  apply lt_of_le_of_lt (Cardinal.power_le_power_right (Cardinal.cantor ξ).le)
  rw [← Cardinal.power_mul]
  exact hΛ.isStrongPrelimit (Cardinal.mul_lt_of_lt hinf hξ hζ)

theorem estimate {Λ ξ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ) (m : ℕ) :
    ∀ χ, ℵ₀ ≤ χ → χ < Λ →
    ∃ μ, ℵ₀ ≤ μ ∧ μ < Λ ∧
      ∀ (X C : Type u) [LinearOrder X],
        WellFounded ((· < ·) : X → X → Prop) → #X = μ → #C ≤ ξ →
        ∀ c : Finset X → C, ∃ Y : Set X, χ ≤ #Y ∧ Homogeneous c m Y := by
  classical
  induction m with
  | zero =>
    intro χ hχinf hχ
    refine ⟨χ, hχinf, hχ, ?_⟩
    intro X C _ _ hX _ c
    refine ⟨Set.univ, ?_, c ∅, ?_⟩
    · simp only [Cardinal.mk_univ, hX, le_refl]
    · intro s _ hs
      rw [Finset.card_eq_zero.1 hs]
  | succ m ih =>
    intro χ hχinf hχ
    obtain ⟨ζ, hζinf, hζ, hζpart⟩ := ih χ hχinf hχ
    let q := max ℵ₀ (ζ * ξ ^ ζ)
    have hinf : ℵ₀ < Λ := hξinf.trans_lt hξ
    have hq : q < Λ := max_lt hinf
      (Cardinal.mul_lt_of_lt hinf.le hζ (power_lt hΛ hinf.le hξ hζ))
    refine ⟨succ q, (le_max_left _ _).trans (le_succ q), hΛ.isSuccLimit.succ_lt hq, ?_⟩
    intro X C _ wX hX hC c
    let J := ζ.ord.ToType
    have hJ : #J = ζ := by simp [J]
    have : Infinite J := Cardinal.aleph0_le_mk_iff.1 (hJ ▸ hζinf)
    have hcode : #(J × (Finset J → C)) < #X := by
      rw [Cardinal.mk_prod, Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.lift_id,
        Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_finset_of_infinite, hJ, hX]
      apply lt_of_le_of_lt _ (lt_succ q)
      apply le_trans _ (le_max_right _ _)
      exact mul_le_mul' le_rfl (Cardinal.power_le_power_right hC)
    obtain ⟨x, r, _, he⟩ := EndHomogeneous.exists_sequence
      (wellFounded_lt (α := J)) wX c hcode
    obtain ⟨Y, hY, hh⟩ := hζpart J C
      (wellFounded_lt (α := J)) hJ hC (fun a => c (insert x (a.image r)))
    refine ⟨r '' Y, ?_, arity_step c x r he hh⟩
    rwa [Cardinal.mk_image_eq r.injective]

end FinitePartition

namespace ThresholdArithmetic

def ξ : Cardinal.{u} := (2 : Cardinal.{u}) ^ (ℵ_ 1)

theorem palette_infinite : ℵ₀ ≤ ξ.{u} :=
  (aleph0_le_aleph 1).trans (Cardinal.cantor _).le

theorem palette_lt : ξ.{u} < tailThreshold.{u} :=
  (lt_succ ξ).trans_le (Cardinal.le_beth_ord _)

theorem index_limit : IsSuccLimit (succ ξ.{u}).ord :=
  Cardinal.isSuccLimit_ord (palette_infinite.trans (le_succ ξ))

theorem strongLimit : tailThreshold.{u}.IsStrongLimit :=
  Cardinal.isStrongLimit_beth.2 index_limit.isSuccPrelimit

theorem cofinality : tailThreshold.{u}.ord.cof = succ ξ.{u} := by
  change ((Cardinal.ord ∘ Cardinal.beth) (succ ξ).ord).cof = succ ξ
  rw [Ordinal.cof_map_of_isNormal (Cardinal.isNormal_ord.comp Cardinal.isNormal_beth) index_limit]
  exact (Cardinal.isRegular_succ palette_infinite).cof_ord

theorem palette_lt_cofinality : ξ.{u} < tailThreshold.{u}.ord.cof := by
  rw [cofinality]
  exact lt_succ _

theorem endpoint_eq_hanf (hCH : CH.{u}) : endpoint.{u} = hanf (ℵ₀ : Cardinal.{u}) := by
  unfold endpoint hanf
  rw [hCH, Cardinal.succ_aleph, Cardinal.ord_aleph]
  congr 2
  norm_num

end ThresholdArithmetic

namespace FinitePartition

variable {X J C : Type u}

theorem Constant.mono {c : Finset X → C} {m : ℕ} {Y Z : Set X} {p : C}
    (hc : Constant c m Y p) (hZY : Z ⊆ Y) : Constant c m Z p :=
  fun s hs => hc s (hs.trans hZY)

theorem Constant.image [DecidableEq X] (c : Finset X → C) (e : J ↪ X) {m : ℕ} {Y : Set J} {p : C}
    (hh : Constant (fun s => c (s.image e)) m Y p) : Constant c m (e '' Y) p := by
  classical
  intro s hs hc
  let t := s.preimage e e.injective.injOn
  have ht : t.image e = s := by
    rw [Finset.image_preimage]
    exact Finset.filter_eq_self.2 (fun a ha => Set.image_subset_range e Y (hs ha))
  rw [← ht]
  apply hh
  · intro a ha
    obtain ⟨b, hb, heq⟩ := hs (Finset.mem_preimage.1 ha)
    exact (e.injective heq) ▸ hb
  · rw [← Finset.card_image_of_injective t e.injective, ht, hc]

theorem inside {Λ ξ : Cardinal.{u}} (hΛ : Λ.IsStrongLimit)
    (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ) (m : ℕ) (χ : Cardinal.{u})
    (hχinf : ℵ₀ ≤ χ) (hχ : χ < Λ) :
    ∃ μ < Λ, ∀ (X C : Type u), #C ≤ ξ → ∀ (Y : Set X), μ ≤ #Y →
      ∀ c : Finset X → C, ∃ Z ⊆ Y, χ ≤ #Z ∧ Homogeneous c m Z := by
  classical
  obtain ⟨μ, _, hμ, ha⟩ := estimate hΛ hξinf hξ m χ hχinf hχ
  refine ⟨μ, hμ, ?_⟩
  intro X C hC Y hY c
  obtain ⟨e⟩ : Nonempty (μ.ord.ToType ↪ Y) :=
    (Cardinal.le_def _ _).1 (by simpa only [Cardinal.mk_ord_toType] using hY)
  let f := e.trans (Function.Embedding.subtype (· ∈ Y))
  obtain ⟨Z, hZ, p, hp⟩ := ha μ.ord.ToType C wellFounded_lt (Cardinal.mk_ord_toType μ)
    hC (fun s => c (s.image f))
  refine ⟨f '' Z, ?_, ?_, p, Constant.image c f hp⟩
  · rintro _ ⟨z, _, rfl⟩
    exact (e z).property
  · rwa [Cardinal.mk_image_eq f.injective]

end FinitePartition

namespace FinitePatterns

open FinitePartition

variable {X C : Type u} (Λ ξ : Cardinal.{u}) (c : ℕ → Finset X → C)

def Prefix (n : ℕ) (p : ℕ → C) (Y : Set X) : Prop :=
  ∀ j < n, Constant (c j) j Y (p j)

def Unbounded (n : ℕ) (p : ℕ → C) : Prop :=
  ∀ χ < Λ, ∃ Y : Set X, χ ≤ #Y ∧ Prefix c n p Y

variable (hΛ : Λ.IsStrongLimit) (hξinf : ℵ₀ ≤ ξ) (hξ : ξ < Λ)
  (hcof : ξ < Λ.ord.cof) (hC : #C ≤ ξ)

include hΛ hξinf hξ hcof hC in

theorem extend (n : ℕ) (p : ℕ → C) (hg : Unbounded Λ c n p) :
    ∃ q : C, Unbounded Λ c (n + 1) (Function.update p n q) := by
  classical
  by_contra hn
  have hb : ∀ q : C, ∃ χ < Λ, ∀ Y : Set X, χ ≤ #Y →
      ¬ Prefix c (n + 1) (Function.update p n q) Y := by
    intro q
    have hq := (not_exists.mp hn) q
    unfold Unbounded at hq
    obtain ⟨χ, hχ⟩ := not_forall.mp hq
    obtain ⟨hχ, hY⟩ := Classical.not_imp.mp hχ
    exact ⟨χ, hχ, fun Y hcard hp => hY ⟨Y, hcard, hp⟩⟩
  choose b hb hfail using hb
  have hsup : (⨆ q, b q) < Λ := Cardinal.iSup_lt_of_lt_cof_ord (hC.trans_lt hcof) hb
  let χ := max ℵ₀ (⨆ q, b q)
  have hχ : χ < Λ := max_lt (hξinf.trans_lt hξ) hsup
  obtain ⟨μ, hμ, hpart⟩ := inside hΛ hξinf hξ n χ (le_max_left _ _) hχ
  obtain ⟨Y, hY, hp⟩ := hg μ hμ
  obtain ⟨Z, hZY, hZ, q, hq⟩ := hpart X C hC Y hY (c n)
  apply hfail q Z
  · exact (le_ciSup_of_le ⟨Λ, fun q hq => by obtain ⟨q, rfl⟩ := hq; exact (hb q).le⟩ q le_rfl).trans
      ((le_max_right _ _).trans hZ)
  · intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | rfl
    · rw [Function.update_of_ne hjn.ne]
      exact (hp j hjn).mono hZY
    · rw [Function.update_self]
      exact hq

variable (hX : Λ ≤ #X)

include hX in
theorem initial (p : ℕ → C) : Unbounded Λ c 0 p := by
  intro χ hχ
  refine ⟨Set.univ, ?_, ?_⟩
  · simpa only [Cardinal.mk_univ] using hχ.le.trans hX
  · intro j hj
    omega

def states : (n : ℕ) → {p : ℕ → C // Unbounded Λ c n p}
  | 0 => ⟨fun _ => c 0 ∅, initial Λ c hX _⟩
  | n + 1 =>
    let s := states n
    let h := extend Λ ξ c hΛ hξinf hξ hcof hC n s.val s.property
    ⟨Function.update s.val n h.choose, h.choose_spec⟩

def colors (n : ℕ) : C := (states Λ ξ c hΛ hξinf hξ hcof hC hX (n + 1)).val n

theorem states_agree (n j : ℕ) (hj : j < n) :
    (states Λ ξ c hΛ hξinf hξ hcof hC hX n).val j =
      colors Λ ξ c hΛ hξinf hξ hcof hC hX j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · change Function.update _ n _ j = _
      rw [Function.update_of_ne h.ne]
      exact ih h
    · rfl

theorem colors_unbounded (n : ℕ) :
    Unbounded Λ c n (colors Λ ξ c hΛ hξinf hξ hcof hC hX) := by
  intro χ hχ
  obtain ⟨Y, hY, hp⟩ := (states Λ ξ c hΛ hξinf hξ hcof hC hX n).property χ hχ
  refine ⟨Y, hY, ?_⟩
  intro j hj
  rw [← states_agree Λ ξ c hΛ hξinf hξ hcof hC hX n j hj]
  exact hp j hj

include hΛ hξinf hξ hcof hC hX in

theorem exists_patterns :
    ∃ p : ℕ → C, ∀ k : ℕ, ∃ A : Finset X, A.card = k ∧
      ∀ j ≤ k, ∀ s ⊆ A, s.card = j → c j s = p j := by
  classical
  refine ⟨colors Λ ξ c hΛ hξinf hξ hcof hC hX, ?_⟩
  intro k
  obtain ⟨Y, hY, hp⟩ := colors_unbounded Λ ξ c hΛ hξinf hξ hcof hC hX
    (k + 1) ℵ₀ (hξinf.trans_lt hξ)
  have hi : Infinite Y := Cardinal.aleph0_le_mk_iff.1 hY
  obtain ⟨A, hA, hc⟩ := (Set.infinite_coe_iff.1 hi).exists_subset_card_eq k
  refine ⟨A, hc, ?_⟩
  intro j hj s hs hsc
  exact hp j (Nat.lt_succ_of_le hj) s ((Finset.coe_subset.2 hs).trans hA) hsc

end FinitePatterns

end CHObstruction

end

end OAI
