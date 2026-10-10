import OAI.Analysis.TreePotential.Normalization

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
/-- Coercion commutes with a bounded real infimum. -/

lemma ereal_coe_ciInf {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddBelow (Set.range f)) :
    ((⨅ i,f i : ℝ) : EReal) = ⨅ i,(f i : EReal) := by
  have hl : ((⨅ i,f i : ℝ) : EReal) ≤ ⨅ i,(f i : EReal) := by
    apply le_iInf
    intro i
    exact EReal.coe_le_coe_iff.mpr (ciInf_le hf i)
  have hb : (⨅ i,(f i : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
  have ht : (⨅ i,(f i : EReal)) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf_le (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have he := EReal.coe_toReal ht hb
  apply le_antisymm hl
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply le_ciInf
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact iInf_le _ i

lemma ereal_coe_ciSup {I : Type*} [Nonempty I] (f : I → ℝ)
    (hf : BddAbove (Set.range f)) :
    ((⨆ i,f i : ℝ) : EReal) = ⨆ i,(f i : EReal) := by
  have hu : (⨆ i,(f i : EReal)) ≤ ((⨆ i,f i : ℝ) : EReal) := by
    apply iSup_le
    intro i
    exact EReal.coe_le_coe_iff.mpr (le_ciSup hf i)
  have hb : (⨆ i,(f i : EReal)) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_iSup (fun i => (f i : EReal)) (Classical.choice inferInstance))
  have ht : (⨆ i,(f i : EReal)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  have he := EReal.coe_toReal ht hb
  apply le_antisymm _ hu
  rw [← he]
  apply EReal.coe_le_coe_iff.mpr
  apply ciSup_le
  intro i
  apply EReal.coe_le_coe_iff.mp
  rw [he]
  exact le_iSup (fun i => (f i : EReal)) i

lemma ereal_coe_modulus_game {X F : Type*} {Y : F → Type*}
    [Nonempty X] [Nonempty F] [∀ f,Nonempty (Y f)]
    (v : X → (f : F) → Y f → ℝ) {a b : ℝ}
    (hl : ∀ x f y,a ≤ v x f y) (hu : ∀ x f,∃ y,v x f y ≤ b) :
    ((⨅ x,⨆ f,⨅ y,v x f y : ℝ) : EReal) =
      ⨅ x,⨆ f,⨅ y,(v x f y : EReal) := by
  have hb x f : BddBelow (Set.range (v x f)) := ⟨a,by rintro _ ⟨y,rfl⟩; exact hl x f y⟩
  have hlo x f : a ≤ ⨅ y,v x f y := le_ciInf (hl x f)
  have hup x f : (⨅ y,v x f y) ≤ b := by
    obtain ⟨y,hy⟩ := hu x f
    exact (ciInf_le (hb x f) y).trans hy
  have hsup x : BddAbove (Set.range (fun f => ⨅ y,v x f y)) :=
    ⟨b,by rintro _ ⟨f,rfl⟩; exact hup x f⟩
  have hmid x : a ≤ ⨆ f,⨅ y,v x f y :=
    (hlo x (Classical.choice inferInstance)).trans (le_ciSup (hsup x) _)
  rw [ereal_coe_ciInf _ ⟨a,by rintro _ ⟨x,rfl⟩; exact hmid x⟩]
  congr 1
  funext x
  rw [ereal_coe_ciSup _ (hsup x)]
  congr 1
  funext f
  exact ereal_coe_ciInf _ (hb x f)

section RealModuli
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : Nonempty (ClosedFiniteCodim E) :=
  ⟨⟨⊤,by simp,inferInstance⟩⟩

lemma ClosedFiniteCodim.unit_exists (hinf : ¬Module.Finite ℝ E)
    (F : ClosedFiniteCodim E) : ∃ y : E,y ∈ F.space ∧ ‖y‖=1 := by
  have hbot : F.space ≠ ⊥ := by
    intro h
    apply hinf
    let := F.finiteCodim
    exact Module.Finite.of_injective F.space.mkQ
      (LinearMap.ker_eq_bot.mp ((Submodule.ker_mkQ _).trans h))
  obtain ⟨v,hv,hvn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨‖v‖⁻¹ • v,F.space.smul_mem _ hv,?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvn)]

/-- The real-valued averaged asymptotic modulus. -/
def averagedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1≤‖y‖},
      (‖x.val+t • y.val‖+‖x.val-t • y.val‖)/((2 : ℕ) : ℝ)-1

def oneSidedModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},‖x.val+t • y.val‖-1

def maximumModulusReal (t : ℝ) : ℝ :=
  ⨅ x : {x : E // ‖x‖=1},⨆ F : ClosedFiniteCodim E,
    ⨅ y : {y : E // y ∈ F.space ∧ 1≤‖y‖},
      max ‖x.val+t • y.val‖ ‖x.val-t • y.val‖-1

def IsAUCReal : Prop := ∀ t : ℝ,0< t → 0< oneSidedModulusReal E t

lemma unit_nonempty_of_infinite (hinf : ¬Module.Finite ℝ E) :
    Nonempty {x : E // ‖x‖=1} := by
  obtain ⟨x,_,hx⟩ := (Classical.choice (inferInstance : Nonempty (ClosedFiniteCodim E))).unit_exists E hinf
  exact ⟨⟨x,hx⟩⟩

lemma unit_perturbation_bound {x y : E} (hx : ‖x‖=1) (hy : ‖y‖=1) (t : ℝ) :
    ‖x+t • y‖ ≤ 1+|t| ∧ ‖x-t • y‖ ≤ 1+|t| := by
  constructor
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_add_le x (t • y)
  · simpa only [hx,hy,norm_smul,Real.norm_eq_abs,mul_one] using norm_sub_le x (t • y)

lemma averagedModulusReal_coe (hinf : ¬Module.Finite ℝ E) (t : ℝ) :
    (averagedModulusReal E t : EReal)=averagedModulus E t := by
  let := unit_nonempty_of_infinite E hinf
  have (F : ClosedFiniteCodim E) : Nonempty {y : E // y ∈ F.space ∧ 1≤‖y‖} := by
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    exact ⟨⟨y,hy,hyn.ge⟩⟩
  apply ereal_coe_modulus_game (a := -1) (b := |t|)
  · intro x F y
    linarith [norm_nonneg (x.val+t • y.val),norm_nonneg (x.val-t • y.val)]
  · intro x F
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    refine ⟨⟨y,hy,hyn.ge⟩,?_⟩
    have hh := unit_perturbation_bound E x.property hyn t
    dsimp
    linarith [hh.1,hh.2]

lemma oneSidedModulusReal_coe (hinf : ¬Module.Finite ℝ E) (t : ℝ) :
    (oneSidedModulusReal E t : EReal)=oneSidedModulus E t := by
  let := unit_nonempty_of_infinite E hinf
  have (F : ClosedFiniteCodim E) : Nonempty {y : E // y ∈ F.space ∧ ‖y‖=1} := by
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    exact ⟨⟨y,hy,hyn⟩⟩
  apply ereal_coe_modulus_game (a := -1) (b := |t|)
  · intro x F y
    linarith [norm_nonneg (x.val+t • y.val)]
  · intro x F
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    refine ⟨⟨y,hy,hyn⟩,?_⟩
    have hh := unit_perturbation_bound E x.property hyn t
    dsimp
    linarith [hh.1]

lemma maximumModulusReal_coe (hinf : ¬Module.Finite ℝ E) (t : ℝ) :
    (maximumModulusReal E t : EReal)=maximumModulus E t := by
  let := unit_nonempty_of_infinite E hinf
  have (F : ClosedFiniteCodim E) : Nonempty {y : E // y ∈ F.space ∧ 1≤‖y‖} := by
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    exact ⟨⟨y,hy,hyn.ge⟩⟩
  apply ereal_coe_modulus_game (a := -1) (b := |t|)
  · intro x F y
    linarith [norm_nonneg (x.val+t • y.val),le_max_left ‖x.val+t • y.val‖ ‖x.val-t • y.val‖]
  · intro x F
    obtain ⟨y,hy,hyn⟩ := F.unit_exists E hinf
    refine ⟨⟨y,hy,hyn.ge⟩,?_⟩
    have hh := unit_perturbation_bound E x.property hyn t
    dsimp
    have hm := max_le hh.1 hh.2
    linarith

lemma isAUCReal_iff (hinf : ¬Module.Finite ℝ E) : IsAUCReal E ↔ IsAUC E := by
  unfold IsAUCReal IsAUC
  have hzero : (0 : EReal)=(0 : ℝ) := by norm_cast
  simp only [← oneSidedModulusReal_coe E hinf,hzero,EReal.coe_lt_coe_iff]

lemma oneSidedModulus_eq_top_of_finite [Module.Finite ℝ E] (t : ℝ) :
    oneSidedModulus E t=⊤ := by
  apply top_unique
  apply le_iInf
  intro x
  let F : ClosedFiniteCodim E := ⟨⊥,by simp,inferInstance⟩
  apply le_trans _ (le_iSup (fun F : ClosedFiniteCodim E =>
    ⨅ y : {y : E // y ∈ F.space ∧ ‖y‖=1},((‖x.val+t • y.val‖-1 : ℝ) : EReal)) F)
  have : IsEmpty {y : E // y ∈ F.space ∧ ‖y‖=1} := by
    constructor
    intro y
    have hy : y.val=0 := y.property.1
    simpa [hy] using y.property.2
  simp

lemma infiniteDimensional_of_not_isAUC (h : ¬IsAUC E) : ¬Module.Finite ℝ E := by
  intro hf
  let := hf
  apply h
  intro t ht
  rw [oneSidedModulus_eq_top_of_finite]
  exact EReal.coe_lt_top 0

lemma not_isAUCReal_of_not_isAUC (h : ¬IsAUC E) : ¬IsAUCReal E :=
  fun hh => h ((isAUCReal_iff E (infiniteDimensional_of_not_isAUC E h)).mp hh)

end RealModuli
end BoundedTreePotentials

end

end OAI
