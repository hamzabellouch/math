import OAI.Algebra.Determinantal.ProjectiveCounts

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical

lemma weight_mapDomain_eq {σ τ G : Type*} [AddCommMonoid G]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    (d : σ →₀ ℕ) : Finsupp.weight w' (d.mapDomain f) = Finsupp.weight w d := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => simp [Finsupp.mapDomain_add, hd, he]
  | single x n => simp [Finsupp.weight_single, hf]

lemma homogeneous_rename {σ τ G R : Type*} [AddCommMonoid G] [CommSemiring R]
    (w : σ → G) (w' : τ → G) (f : σ → τ) (hf : ∀ x, w' (f x) = w x)
    {p : MvPolynomial σ R} {d : G} (hp : p.IsWeightedHomogeneous w d) :
    (rename f p).IsWeightedHomogeneous w' d := by
  conv_lhs => rw [as_sum p]
  rw [map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ ((weight_mapDomain_eq w w' f hf m).trans
    (hp (mem_support_iff.mp hm)))

section Reindex
variable {ι σ E L V : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ]
  [Fintype E] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem bilinear_simple_point_count_reindex (a : ι →₀ ℕ)
    (group : σ → ι) (ve : σ ≃ BlockVariables a)
    (hv : ∀ s, (ve s).1 = group s)
    (u v : E → ι) (hM : Fintype.card E = ∑ j, a j)
    (F : E → MvPolynomial σ ℂ)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (blockWeight group)
      (Pi.single (u i) 1 + Pi.single (v i) 1))
    (base : L → ι → σ) (hbase : ∀ i j, group (base i j) = j)
    (e : L → (E → ℂ) ≃L[ℂ] V)
    (chart : L → V → σ → ℂ) (hc : ∀ i, ContDiff ℂ 1 (chart i))
    (hcn : ∀ i z j, chart i z (base i j) = 1)
    (x : L → V)
    (hx : ∀ i j, i ≠ j → BlockSeparated group (chart i (x i)) (chart j (x j)))
    (hz : ∀ i j, eval (chart i (x i)) (F j) = 0)
    (hs : ∀ i, (fderiv ℂ (fun z => e i (fun j => eval (chart i z) (F j)))
      (x i)).IsInvertible) :
    Fintype.card L ≤ (mixedPolynomial u v).coeff a := by
  classical
  let ee := (Fintype.equivFin E).symm
  let ec : (Fin (Fintype.card E) → ℂ) ≃L[ℂ] (E → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : E => ℂ) ee
  let F' (i : Fin (Fintype.card E)) := rename ve (F (ee i))
  let chart' (i : L) (z : V) : BlockVariables a → ℂ := chart i z ∘ ve.symm
  have hc' (i : L) : ContDiff ℂ 1 (chart' i) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_apply ℂ ℂ (ve.symm j)).comp (hc i)
  have heval (i : L) (z : V) (j : Fin (Fintype.card E)) :
      eval (chart' i z) (F' j) = eval (chart i z) (F (ee j)) := by
    dsimp only [F']
    rw [eval_rename]
    apply congrArg (fun v : σ → ℂ => eval v (F (ee j)))
    funext s
    simp [chart']
  have hs' (i : L) : (fun z => (ec.trans (e i)) (fun j => eval (chart' i z) (F' j))) =
      fun z => e i (fun j => eval (chart i z) (F j)) := by
    funext z
    simp only [ContinuousLinearEquiv.trans_apply]
    apply congrArg (e i)
    funext j
    change (Homeomorph.piCongrLeft (Y := fun _ : E => ℂ) ee)
      (fun j => eval (chart' i z) (F' j)) j = _
    conv_lhs => rw [← ee.apply_symm_apply j]
    rw [Homeomorph.piCongrLeft_apply_apply, heval, ee.apply_symm_apply]
  have hh := bilinear_simple_point_count_multichart a (u ∘ ee) (v ∘ ee) hM F'
    (fun i => homogeneous_rename _ _ ve (fun s => by simp [blockWeight, hv]) (hF (ee i)))
    (fun i j => ve (base i j)) (fun i j => (hv _).trans (hbase i j))
    (fun i => ec.trans (e i)) chart' hc'
    (fun i z j => by simpa [chart'] using hcn i z j) x
    (fun i j hij => by
      obtain ⟨s,t,hst,hne⟩ := hx i j hij
      refine ⟨ve s,ve t,?_,?_⟩
      · simpa [hv] using hst
      · simpa [chart'] using hne)
    (fun i j => (heval i (x i) j).trans (hz i (ee j)))
    (fun i => by rw [hs']; exact hs i)
  have hm : mixedPolynomial (u ∘ ee) (v ∘ ee) = mixedPolynomial u v := by
    exact Fintype.prod_equiv ee _ _ (fun _ => rfl)
  rwa [hm] at hh
end Reindex
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

abbrev Groups := Option Bool
abbrev Var (κ : Type) (n : ℕ) : Groups → Type _ :=
  Option.elim' (Option (Option κ)) (fun _ => Fin (n+1))
instance varFintype (κ : Type) [Fintype κ] (n : ℕ) : (j : Groups) → Fintype (Var κ n j)
  | none => inferInstanceAs (Fintype (Option (Option κ)))
  | some _ => inferInstanceAs (Fintype (Fin (n+1)))
abbrev Variables (κ : Type) (n : ℕ) := Σ j : Groups, Var κ n j
abbrev Equations (κ : Type) (n : ℕ) := Fin (n+1) ⊕ (Fin n ⊕ κ)

variable {κ : Type} [Fintype κ] {n : ℕ}

noncomputable def dimensions (κ : Type) [Fintype κ] (n : ℕ) : Groups →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Option.elim' (Fintype.card κ+1) (fun _ => n))

@[simp] lemma dimensions_none : dimensions κ n none = Fintype.card κ+1 := rfl
@[simp] lemma dimensions_some (b : Bool) : dimensions κ n (some b) = n := rfl

lemma var_card (j : Groups) : Fintype.card (Var κ n j) = dimensions κ n j + 1 := by
  cases j with
  | none =>
    change Fintype.card (Option (Option κ)) = Fintype.card κ + 1 + 1
    exact Fintype.card_option.trans (congrArg (fun k => k+1) Fintype.card_option)
  | some b =>
    change Fintype.card (Fin (n+1)) = n+1
    exact Fintype.card_fin _

noncomputable def variablesEquiv : Variables κ n ≃
    Multigraded.BlockVariables (dimensions κ n) :=
  Equiv.sigmaCongrRight (fun j => (Fintype.equivFin (Var κ n j)).trans
    (finCongr (var_card j)))

@[simp] lemma variablesEquiv_group (s : Variables κ n) :
    (variablesEquiv s).1 = s.1 := rfl

noncomputable def linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  C (A₀ i j) * X ⟨none,none⟩ + ∑ k, C (A k i j) * X ⟨none,some k⟩

noncomputable def rightEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ j, linearMatrix A₀ A i j * X ⟨some false,j⟩

noncomputable def leftEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ i, linearMatrix A₀ A i j * X ⟨some true,i⟩

noncomputable def polarEquation (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    MvPolynomial (Variables κ n) ℂ :=
  ∑ i, ∑ j, C (B i j) * X ⟨some false,j⟩ * X ⟨some true,i⟩

noncomputable def system (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1)) :
    Equations κ n → MvPolynomial (Variables κ n) ℂ :=
  Sum.elim (rightEquation A₀ A)
    (Sum.elim (fun j => leftEquation A₀ A (pivot.succAbove j)) (fun k => polarEquation (B k)))

def firstGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (fun _ => some false))
def secondGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => some false) (Sum.elim (fun _ => some true) (fun _ => some true))

lemma linearMatrix_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin (n+1)) :
    (linearMatrix A₀ A i j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single none 1) := by
  apply IsWeightedHomogeneous.add
  · exact (isWeightedHomogeneous_X ℂ _ _).C_mul _
  · exact IsWeightedHomogeneous.sum _ _ _ (fun k _ => (isWeightedHomogeneous_X ℂ _ _).C_mul _)

lemma right_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i : Fin (n+1)) :
    (rightEquation A₀ A i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some false) 1) := by
  unfold rightEquation
  apply IsWeightedHomogeneous.sum
  intro j _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n))

lemma left_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (j : Fin (n+1)) :
    (leftEquation A₀ A j).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (none : Groups) 1 + Pi.single (some true) 1) := by
  unfold leftEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  exact (linearMatrix_homogeneous A₀ A i j).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

omit [Fintype κ] in
lemma polar_homogeneous (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    (polarEquation (κ := κ) B).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (some false : Groups) 1 + Pi.single (some true) 1) := by
  unfold polarEquation
  apply IsWeightedHomogeneous.sum
  intro i _
  apply IsWeightedHomogeneous.sum
  intro j _
  exact ((isWeightedHomogeneous_X ℂ _ (⟨some false,j⟩ : Variables κ n)).C_mul (B i j)).mul
    (isWeightedHomogeneous_X ℂ _ (⟨some true,i⟩ : Variables κ n))

lemma system_homogeneous (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1))
    (i : Equations κ n) :
    (system A₀ A B pivot i).IsWeightedHomogeneous (Multigraded.blockWeight Sigma.fst)
      (Pi.single (firstGroup i) 1 + Pi.single (secondGroup i) 1) := by
  rcases i with i | j | k
  · exact right_homogeneous A₀ A i
  · exact left_homogeneous A₀ A (pivot.succAbove j)
  · exact polar_homogeneous (B k)

lemma card_equations : Fintype.card (Equations κ n) = ∑ j, dimensions κ n j := by
  simp [Equations, Fintype.sum_option]
  omega

noncomputable def coordinates (z : Option κ → ℂ)
    (u v : Fin (n+1) → ℂ) : Variables κ n → ℂ :=
  fun s => match s with
    | ⟨none,t⟩ => t.elim 1 z
    | ⟨some false,i⟩ => u i
    | ⟨some true,i⟩ => v i

@[simp] lemma eval_linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i j : Fin (n+1)) :
    eval (coordinates z u v) (linearMatrix A₀ A i j) = A₀ i j + ∑ k, A k i j * z k := by
  simp [linearMatrix, coordinates]

@[simp] lemma eval_right (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    eval (coordinates z u v) (rightEquation A₀ A i) =
      ∑ j, (A₀ i j + ∑ k, A k i j * z k) * u j := by
  simp [rightEquation, coordinates]

@[simp] lemma eval_left (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (j : Fin (n+1)) :
    eval (coordinates z u v) (leftEquation A₀ A j) =
      ∑ i, (A₀ i j + ∑ k, A k i j * z k) * v i := by
  simp [leftEquation, coordinates]

omit [Fintype κ] in
@[simp] lemma eval_polar (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) :
    eval (coordinates z u v) (polarEquation B) = ∑ i, ∑ j, B i j * u j * v i := by
  simp [polarEquation, coordinates]

lemma mixedPolynomial_eq :
    Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup =
      (X none + X (some false))^(n+1) * (X none + X (some true))^n *
        (X (some false) + X (some true))^Fintype.card κ := by
  simp [Multigraded.mixedPolynomial, firstGroup, secondGroup, Fintype.prod_sum_type,
    mul_assoc]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
noncomputable def collapse (i : σ) : MvPolynomial σ ℕ →+* Polynomial ℕ :=
  eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else 1)

lemma collapse_monomial (i : σ) (d : σ →₀ ℕ) (a : ℕ) :
    collapse i (monomial d a) = Polynomial.C a * Polynomial.X^(d i) := by
  rw [collapse, eval₂Hom_monomial]
  congr 1
  have h := Finsupp.prod_ite_eq d i (fun _ n => (Polynomial.X : Polynomial ℕ)^n)
  by_cases hi : i ∈ d.support
  · simpa only [ite_eq_left hi, eq_comm, ite_pow, one_pow] using h
  · simpa only [ite_eq_right hi, Finsupp.notMem_support_iff.mp hi, pow_zero,
      eq_comm, ite_pow, one_pow] using h

lemma coeff_le_collapse (i : σ) (p : MvPolynomial σ ℕ) (d : σ →₀ ℕ) :
    p.coeff d ≤ (collapse i p).coeff (d i) := by
  by_cases hd : d ∈ p.support
  · have he : (collapse i p).coeff (d i) =
        ∑ k ∈ p.support, (collapse i (monomial k (p.coeff k))).coeff (d i) := by
      conv_lhs => rw [as_sum p]
      simp only [map_sum, Polynomial.finsetSum_coeff]
    rw [he]
    have h := Finset.single_le_sum (fun k (_ : k ∈ p.support) =>
      Nat.zero_le ((collapse i (monomial k (p.coeff k))).coeff (d i))) hd
    simpa [collapse_monomial, Polynomial.coeff_C_mul] using h
  · rw [notMem_support_iff.mp hd]
    exact Nat.zero_le _
end PermanentBorder.Multigraded

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
lemma mixed_coefficient_bound :
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
      (dimensions κ n) ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by
  have h := Multigraded.coeff_le_collapse none
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup)
    (dimensions κ n)
  have hp : Multigraded.collapse none
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup) =
      (Polynomial.X + 1)^(2*n+1) * Polynomial.C (2^Fintype.card κ) := by
    rw [mixedPolynomial_eq]
    simp only [map_mul, map_pow, map_add, Multigraded.collapse, eval₂Hom_X']
    simp only [↓reduceIte, Option.some_ne_none, one_add_one_eq_two]
    rw [← pow_add, show n+1+n = 2*n+1 by omega]
    simp
  rw [hp, dimensions_none, Polynomial.coeff_mul_C, Polynomial.coeff_X_add_one_pow,
    mul_comm] at h
  exact h
end PermanentBorder.KernelBilinear

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Elimination
variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

 theorem isInvertible_of_injective (T : V →L[ℂ] V) (hT : Function.Injective T) :
    T.IsInvertible := by
  have hs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  obtain ⟨u, hu⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hT,hs⟩
  exact ⟨ContinuousLinearEquiv.ofUnit u,hu⟩

theorem invertible_elimination (R : (V × W) →L[ℂ] V) (E : (V × W) →L[ℂ] W)
    (g : V →L[ℂ] W)
    (hE : (E ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (he : E ∘L ((ContinuousLinearMap.id ℂ V).prod g) = 0)
    (hR : (R ∘L ((ContinuousLinearMap.id ℂ V).prod g)).IsInvertible) :
    (R.prod E).IsInvertible := by
  apply isInvertible_of_injective
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro z hz
  have hrz : R z = 0 := congrArg Prod.fst hz
  have hez : E z = 0 := congrArg Prod.snd hz
  have heg : E (z.1,g z.1) = 0 := by
    have h := congrArg (fun T : (V →L[ℂ] W) => T z.1) he
    simpa using h
  have hsub : E (0,z.2-g z.1) = 0 := by
    have hh : (0,z.2-g z.1) = z - (z.1,g z.1) := by ext <;> simp
    rw [hh, map_sub,hez,heg,sub_self]
  have hdw : z.2 = g z.1 := by
    have hm : (E ∘L ContinuousLinearMap.inr ℂ V W) (z.2-g z.1) =
        (E ∘L ContinuousLinearMap.inr ℂ V W) 0 := by
      rw [map_zero]
      exact hsub
    exact sub_eq_zero.mp (hE.bijective.injective hm)
  have hdx : z.1 = 0 := by
    apply hR.bijective.injective
    rw [map_zero]
    change R (z.1,g z.1) = 0
    simpa only [← hdw,Prod.eta] using hrz
  exact Prod.ext hdx (by simpa [hdx] using hdw)

theorem simple_after_elimination {R : V × W → V} {E : V × W → W}
    {g : V → W} {x : V}
    (hR : DifferentiableAt ℂ R (x,g x)) (hE : DifferentiableAt ℂ E (x,g x))
    (hg : DifferentiableAt ℂ g x)
    (he : (fun y => E (y,g y)) =ᶠ[𝓝 x] 0)
    (haux : (fderiv ℂ E (x,g x) ∘L ContinuousLinearMap.inr ℂ V W).IsInvertible)
    (hs : (fderiv ℂ (fun y => R (y,g y)) x).IsInvertible) :
    (fderiv ℂ (fun z => (R z,E z)) (x,g x)).IsInvertible := by
  let graph := (ContinuousLinearMap.id ℂ V).prod (fderiv ℂ g x)
  have hgraph : HasFDerivAt (fun y => (y,g y)) graph x :=
    (hasFDerivAt_id x).prodMk hg.hasFDerivAt
  have he' : fderiv ℂ E (x,g x) ∘L graph = 0 := by
    have hd := hE.hasFDerivAt.comp x hgraph
    have hz := (hasFDerivAt_const (𝕜 := ℂ) (0 : W) x).congr_of_eventuallyEq he
    exact hd.unique hz
  have hr' : (fderiv ℂ R (x,g x) ∘L graph).IsInvertible := by
    have hd := hR.hasFDerivAt.comp x hgraph
    rwa [← hd.fderiv]
  rw [(hR.hasFDerivAt.prodMk hE.hasFDerivAt).fderiv]
  exact invertible_elimination _ _ _ haux he' hr'
end Elimination
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks (Matrix.of fun _ _ => a) (Matrix.of fun _ j => β j) (Matrix.of fun i _ => γ i) E
noncomputable def right (γ : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(E⁻¹ *ᵥ γ)
noncomputable def left (β : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(β ᵥ* E⁻¹)
noncomputable def scalar (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) : ℂ :=
  a - β ⬝ᵥ (E⁻¹ *ᵥ γ)
noncomputable def normalized (u : ι → ℂ) : Unit ⊕ ι → ℂ := Sum.elim (fun _ => 1) u

 theorem solved_right (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    block a β γ E *ᵥ normalized (right γ E) =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, fromBlocks_mulVec, right, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : E *ᵥ -(E⁻¹ *ᵥ γ) = -γ := by
    rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv E hu, one_mulVec]
  rw [hh]
  ext j
  cases j <;> simp [scalar, mulVec, dotProduct, Finset.mul_sum, sub_eq_add_neg]

 theorem solved_left (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    normalized (left β E) ᵥ* block a β γ E =
      Sum.elim (fun _ => scalar a β γ E) (fun _ => 0) := by
  have hu : IsUnit E.det := isUnit_iff_ne_zero.mpr hE
  simp only [block, normalized, vecMul_fromBlocks, left, Sum.elim_comp_inl, Sum.elim_comp_inr]
  have hh : -(β ᵥ* E⁻¹) ᵥ* E = -β := by
    rw [neg_vecMul, vecMul_vecMul, nonsing_inv_mul E hu, vecMul_one]
  rw [hh]
  ext j
  cases j with
  | inl u =>
    simp only [Sum.elim_inl, Pi.add_apply, vecMul, dotProduct, Matrix.of_apply,
      Fintype.sum_unique, one_mul, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      scalar, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, sub_eq_add_neg]
    rw [Finset.sum_comm]
  | inr j => simp [vecMul, dotProduct]

 theorem det_block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) (hE : E.det ≠ 0) :
    (block a β γ E).det = E.det * scalar a β γ E := by
  let := E.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hE)
  rw [block, det_fromBlocks₂₂]
  congr 1
  rw [Matrix.det_eq_elem_of_subsingleton _ ()]
  simp only [Matrix.sub_apply, Matrix.mul_apply, scalar]
  simp only [invOf_eq_nonsing_inv, Matrix.of_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

 theorem differentiableAt_det {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) :
    DifferentiableAt ℂ (fun y => (E y).det) x := by
  classical
  simp only [Matrix.det_apply]
  fun_prop

 theorem differentiableAt_adjugate {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  apply differentiableAt_det
  intro u v
  by_cases hu : u = j
  · subst u
    simp only [Matrix.updateRow_self]
    exact differentiableAt_const _
  · simpa only [Matrix.updateRow_ne hu] using hE u v

 theorem differentiableAt_inverse {E : V → Matrix ι ι ℂ} {x : V}
    (hE : ∀ i j, DifferentiableAt ℂ (fun y => E y i j) x)
    (hx : (E x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℂ (fun y => (E y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((differentiableAt_det hE).inv hx).mul (differentiableAt_adjugate hE i j)
end Calculus
end PermanentBorder.PolarAnalysis.Schur

end OAI
