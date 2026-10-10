import OAI.Probability.TraceReconstruction.InitialOverlap

namespace OAI

/-!
# LeafOracle

Recursive leaf oracles, sparse high tails, occupied shapes, posterior smoothing, source bit trees, and singleton cancellation.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Complete window-tree leaf indices, with counts numbered from the bottom.
The tree is fixed before any occupied subset or orientation is selected. -/
def WindowLeaf (T : ℕ → ℕ) : ℕ → Type
  | 0 => Fin 1
  | b+1 => Fin (T b) × WindowLeaf T b

noncomputable instance windowLeafFintype (T : ℕ → ℕ) : (b : ℕ) → Fintype (WindowLeaf T b)
  | 0 => inferInstanceAs (Fintype (Fin 1))
  | b+1 => by
    letI := windowLeafFintype T b
    exact inferInstanceAs (Fintype (Fin (T b) × WindowLeaf T b))

/-- A motif's actual outgoing type, allowing every integer displacement. -/
def motifChildSign (s : ℕ) (X : ℤ) (h : ℕ) (τ : ℝ) : ℝ :=
  1-motifIndicator s ((h:ℤ)-X)+(prouhetSeries s).coeff ((h:ℤ)-X)*τ

theorem motifChildSign_isSign (s : ℕ) (X : ℤ) (h : ℕ) {τ : ℝ} (hτ : IsTypeSign τ) :
    IsTypeSign (motifChildSign s X h τ) :=
  motif_child_sign (prouhet_motif_value s ((h:ℤ)-X)) hτ

theorem motifChildSign_negative_active (s : ℕ) (X : ℤ) (h : ℕ) (τ : ℝ)
    (ht : motifChildSign s X h τ= -1) : 0 ≤ (h:ℤ)-X ∧ (h:ℤ)-X<(2^s:ℕ) := by
  by_contra hn
  have hz := (prouhetSeries_coeff_spec s).1 ((h:ℤ)-X) (by omega)
  simp only [motifChildSign,motifIndicator,ite_eq_right hn,hz,zero_mul,sub_zero,add_zero] at ht
  norm_num at ht

/-- Literal top-down type recursion in the source's unconditioned surrogate.
`X path` is the root anchor or `w_j-Y_path`. Dependence of different paths
through the same global jitter is retained by this single full-tree map. -/
def windowLeafSign (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → List ℕ → ℝ → WindowLeaf T b → ℝ
  | 0, _, τ, _ => τ
  | b+1, path, τ, v => windowLeafSign T s X b (path++[v.1.val])
      (motifChildSign s (X path) v.1.val τ) v.2

theorem windowLeafSign_isSign (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) {τ : ℝ} (hτ : IsTypeSign τ) (v : WindowLeaf T b) :
    IsTypeSign (windowLeafSign T s X b path τ v) := by
  induction b generalizing path τ with
  | zero => exact hτ
  | succ b ih => exact ih _ (motifChildSign_isSign s _ _ hτ) v.2

def windowLeafType (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) (v : WindowLeaf T b) : Bool :=
  decide (windowLeafSign T s X b path τ v= -1)

theorem windowLeafType_weight (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) {τ : ℝ} (hτ : IsTypeSign τ) (v : WindowLeaf T b) :
    (if windowLeafType T s X b path τ v then (1:ℝ) else 0)=
      (1-windowLeafSign T s X b path τ v)/2 := by
  rcases windowLeafSign_isSign T s X b path hτ v with hp | hm
  · norm_num [windowLeafType,hp]
  · norm_num [windowLeafType,hm]

/-- A finite indexing of all leaves, not just the active or fitted leaves. -/
def windowFinType (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (τ : ℝ) (i : Fin (Fintype.card (WindowLeaf T b))) : Bool :=
  windowLeafType T s X b [] τ ((Fintype.equivFin (WindowLeaf T b)).symm i)

/-- The actual mixed leaf oracle at arbitrary exact metadata. The one latent
law governs the whole map X; no independent-anchor law is substituted. -/
def recursiveLeafLaw {Ω α : Type*} [Fintype Ω] [Fintype α]
    (R : FiniteLaw Ω) (X : Ω → List ℕ → ℤ) (T : ℕ → ℕ) (s b : ℕ)
    (P Q : FiniteLaw α) (τ : ℝ) :
    FiniteLaw (Fin (Fintype.card (WindowLeaf T b)) → α) :=
  R.mixture (fun ω => coordinateProduct (fun i => if windowFinType T s (X ω) b τ i then Q else P))

theorem recursiveLeafLaw_density {Ω α : Type*} [Fintype Ω] [Fintype α]
    (R : FiniteLaw Ω) (X : Ω → List ℕ → ℤ) (T : ℕ → ℕ) (s b : ℕ)
    (P Q : FiniteLaw α) (Z : α → ℝ) (hZ : ∀a,Q.mass a=P.mass a*(1+Z a))
    (τ : ℝ) (x : Fin (Fintype.card (WindowLeaf T b)) → α) :
    (recursiveLeafLaw R X T s b P Q τ).mass x =
      (P.product (Fintype.card (WindowLeaf T b))).mass x *
        multilinear (averagedCoefficient R (fun ω => windowFinType T s (X ω) b τ)) Z x := by
  rw [recursiveLeafLaw,leaf_oracle_density P Q Z hZ,averagedDensity_expansion]
  rfl

/-- Pointwise recursive coefficient before averaging over the actual bits. -/
theorem recursive_selectionCoefficient {Ω : Type*} [Fintype Ω]
    (X : Ω → List ℕ → ℤ) (T : ℕ → ℕ) (s b : ℕ) (ω : Ω)
    {τ : ℝ} (hτ : IsTypeSign τ) (σ : Fin (Fintype.card (WindowLeaf T b)) → Bool) :
    selectionCoefficient (windowFinType T s (X ω) b τ) σ =
      ∏i, if σ i then
        (1-windowLeafSign T s (X ω) b [] τ ((Fintype.equivFin (WindowLeaf T b)).symm i))/2 else 1 := by
  unfold selectionCoefficient
  apply Finset.prod_congr rfl
  intro i _
  cases σ i
  · rfl
  · exact windowLeafType_weight T s (X ω) b [] hτ _

theorem motif_negative_count (s N : ℕ) (X : ℤ) (τ : ℝ) :
    (Finset.univ.filter (fun i : Fin N => motifChildSign s X i.val τ= -1)).card ≤ 2^s := by
  have H := Finset.card_le_card_of_injOn
    (s:=Finset.univ.filter (fun i : Fin N => motifChildSign s X i.val τ= -1))
    (t:=Finset.range (2^s)) (fun i : Fin N => ((i.val:ℤ)-X).toNat) ?_ ?_
  · simpa using H
  · intro i hi
    have h := motifChildSign_negative_active s X i.val τ (Finset.mem_filter.mp hi).2
    apply Finset.mem_range.mpr
    dsimp only
    omega
  · intro i hi j hj he
    have h := motifChildSign_negative_active s X i.val τ (Finset.mem_filter.mp hi).2
    have h' := motifChildSign_negative_active s X j.val τ (Finset.mem_filter.mp hj).2
    apply Fin.ext
    dsimp only at he
    omega

/-- Exact number of minus leaves in a fixed realization, without a fit condition. -/
def windowMinusCount (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) : ℕ :=
  ∑v : WindowLeaf T b, if windowLeafSign T s X b path τ v= -1 then 1 else 0

theorem windowMinusCount_succ (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) :
    windowMinusCount T s X (b+1) path τ =
      ∑i : Fin (T b), windowMinusCount T s X b (path++[i.val])
        (motifChildSign s (X path) i.val τ) := by
  unfold windowMinusCount
  change (∑v : Fin (T b) × WindowLeaf T b, _) = _
  rw [Fintype.sum_prod_type]
  rfl

/-- Source the block layout high-degree budget, bottom motif length times all
upper window counts. It holds for every latent realization, typical or not. -/
theorem windowMinusCount_bound (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (τ : ℝ) :
    windowMinusCount T s X (b+1) path τ ≤
      2^s * ∏j∈Finset.range b, T (j+1) := by
  induction b generalizing path τ with
  | zero =>
    rw [windowMinusCount_succ]
    change (∑i : Fin (T 0), ∑v : Fin 1,
      if motifChildSign s (X path) i.val τ= -1 then (1:ℕ) else 0) ≤ _
    simp only [Fin.sum_univ_one,Finset.range_zero,Finset.prod_empty,mul_one]
    simpa only [Finset.card_filter] using motif_negative_count s (T 0) (X path) τ
  | succ b ih =>
    rw [windowMinusCount_succ]
    calc
      _ ≤ ∑i : Fin (T (b+1)), 2^s*∏j∈Finset.range b,T (j+1) :=
        Finset.sum_le_sum (fun _ _ => ih _ _)
      _ = _ := by simp [Finset.prod_range_succ]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def boolSupport {n : ℕ} (θ : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => θ i=true)

theorem boolSupport_injective {n : ℕ} : Function.Injective (boolSupport (n:=n)) := by
  intro θ φ h
  funext i
  have hi : (θ i=true) ↔ (φ i=true) := by
    simpa [boolSupport] using Finset.ext_iff.mp h i
  cases hθ : θ i <;> cases hφ : φ i <;> simp_all

theorem selectionCoefficient_eq_support {n : ℕ} (θ σ : Fin n → Bool) :
    selectionCoefficient θ σ = if boolSupport σ ⊆ boolSupport θ then 1 else 0 := by
  by_cases h : boolSupport σ ⊆ boolSupport θ
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    cases hs : σ i
    · simp
    · have ht : θ i=true := by simpa [boolSupport] using h (by simp [boolSupport,hs])
      simp [ht]
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hni⟩ := Finset.not_subset.mp h
    have hs : σ i=true := by simpa [boolSupport] using hi
    have ht : θ i=false := by simpa [boolSupport] using hni
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hs,ht]

/-- Uniform cardinality bound for the actual selected monomials of a sparse
0/1 coefficient vector; mixing does not add a squared-cardinality loss. -/
theorem selection_degree_sum_le {n : ℕ} (θ : Fin n → Bool) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then selectionCoefficient θ σ else 0) ≤
      ((monomialDegree θ).choose r:ℝ) := by
  have hc : (Finset.univ.filter (fun σ : Fin n → Bool =>
      monomialDegree σ=r ∧ boolSupport σ ⊆ boolSupport θ)).card ≤
        ((boolSupport θ).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn boolSupport
    · intro σ hσ
      rcases (Finset.mem_filter.mp hσ).2 with ⟨hd,hs⟩
      exact Finset.mem_powersetCard.mpr ⟨hs,hd⟩
    · exact boolSupport_injective.injOn
  rw [Finset.card_powersetCard] at hc
  have he : (∑σ : Fin n → Bool, if monomialDegree σ=r then selectionCoefficient θ σ else 0) =
      ((Finset.univ.filter (fun σ : Fin n → Bool =>
        monomialDegree σ=r ∧ boolSupport σ ⊆ boolSupport θ)).card:ℝ) := by
    simp_rw [selectionCoefficient_eq_support,←ite_and]
    exact Finset.sum_boole _ _
  rw [he]
  exact_mod_cast hc

theorem averaged_sparse_degree {Ω : Type*} [Fintype Ω] {n A : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (hA : ∀ω, monomialDegree (θ ω) ≤ A) (r : ℕ) :
    (∑σ : Fin n → Bool, if monomialDegree σ=r then averagedCoefficient R θ σ^2 else 0) ≤
      (A.choose r:ℝ) := by
  calc
    _ ≤ ∑σ : Fin n → Bool, if monomialDegree σ=r then averagedCoefficient R θ σ else 0 := by
      apply Finset.sum_le_sum
      intro σ _
      split_ifs
      · have hc := coefficient_nonneg R θ σ
        have h1 := coefficient_le_one R θ σ
        nlinarith [mul_nonneg hc (sub_nonneg.mpr h1)]
      · rfl
    _ = ∑ω, R.mass ω * ∑σ : Fin n → Bool,
        if monomialDegree σ=r then selectionCoefficient (θ ω) σ else 0 := by
      unfold averagedCoefficient FiniteLaw.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro σ _
      by_cases h : monomialDegree σ=r <;> simp [h]
    _ ≤ ∑ω, R.mass ω * (A.choose r:ℝ) := by
      apply Finset.sum_le_sum
      intro ω _
      apply mul_le_mul_of_nonneg_left _ (R.nonneg ω)
      exact (selection_degree_sum_le (θ ω) r).trans (by
        exact_mod_cast Nat.choose_le_choose r (hA ω))
    _ = _ := by rw [←Finset.sum_mul,R.total,one_mul]

/-- Genuine sparse complete-tree leaf count in the exact Fin indexing used
by the independent-product reference law. -/
theorem windowFinType_degree (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (τ : ℝ) :
    monomialDegree (windowFinType T s X b τ) = windowMinusCount T s X b [] τ := by
  have h := Equiv.sum_comp (Fintype.equivFin (WindowLeaf T b)).symm
    (fun v => if windowLeafSign T s X b [] τ v= -1 then (1:ℕ) else 0)
  simpa only [monomialDegree,Finset.card_filter,windowFinType,windowLeafType,
    decide_eq_true_eq,windowMinusCount] using h

theorem recursive_degree_bound {Ω : Type*} [Fintype Ω]
    (R : FiniteLaw Ω) (X : Ω → List ℕ → ℤ) (T : ℕ → ℕ) (s b r : ℕ) (τ : ℝ) :
    (∑σ, if monomialDegree σ=r then
      averagedCoefficient R (fun ω => windowFinType T s (X ω) (b+1) τ) σ^2 else 0) ≤
        ((2^s*∏j∈Finset.range b,T (j+1)).choose r:ℝ) := by
  apply averaged_sparse_degree
  intro ω
  rw [windowFinType_degree]
  exact windowMinusCount_bound T s (X ω) b [] τ

def degreeTail {n : ℕ} (A : (Fin n → Bool) → ℝ) (k : ℕ) (σ : Fin n → Bool) : ℝ :=
  if k ≤ monomialDegree σ then A σ else 0

theorem degreeTail_degree {n r k : ℕ} (A : (Fin n → Bool) → ℝ) :
    (∑σ, if monomialDegree σ=r then degreeTail A k σ^2 else 0) =
      if k ≤ r then ∑σ, if monomialDegree σ=r then A σ^2 else 0 else 0 := by
  by_cases h : k ≤ r
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : monomialDegree σ=r <;> simp [degreeTail,he,h]
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro σ _
    by_cases he : monomialDegree σ=r <;> simp [degreeTail,he,h]

/-- Geometric high-degree energy of an actual mixed sparse leaf law. -/
theorem averaged_sparse_tail_energy {Ω : Type*} [Fintype Ω] {n A₀ : ℕ}
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (hA : ∀ω, monomialDegree (θ ω) ≤ A₀) (k : ℕ) {w : ℝ}
    (hw : 0 ≤ w) (ha : w^2*A₀ < 1) :
    multilinearEnergy (degreeTail (averagedCoefficient R θ) k) w ≤
      (w^2*A₀)^k/(1-w^2*A₀) := by
  have H := multilinearEnergy_low_high (R:=k)
    (degreeTail (averagedCoefficient R θ) k) w (w^2*A₀) 1 hw (by positivity) ha
    (by norm_num) (fun _ => 0) ?_ ?_ (fun _ => le_rfl)
  · simpa using H
  · intro r hr
    rw [degreeTail_degree,ite_eq_right (by omega)]
  · intro r hr
    rw [degreeTail_degree,ite_eq_left hr,one_mul]
    have hc : (A₀.choose r:ℝ) ≤ (A₀:ℝ)^r := by exact_mod_cast Nat.choose_le_pow A₀ r
    calc
      _ ≤ w^(2*r)*(A₀:ℝ)^r := mul_le_mul_of_nonneg_left
        ((averaged_sparse_degree R θ hA r).trans hc) (by positivity)
      _ = _ := by rw [pow_mul,mul_pow]

/-- Actual recursive-oracle high tail, including arbitrary correlated latent
bits and displacements. This supplies the block layout's unconditioned high-degree
input; low degrees still require the signed occupied-tree cancellation. -/
theorem recursive_high_moment {Ω α : Type*} [Fintype Ω] [Fintype α]
    (R : FiniteLaw Ω) (X : Ω → List ℕ → ℤ) (T : ℕ → ℕ) (s b r₀ k : ℕ) (τ : ℝ)
    (P : FiniteLaw α) (Z : α → ℝ) (hk : 1 ≤ k) (hcenter : P.expect Z=0)
    {L : ℝ} (hL : 0 < L) (hMoment : P.expect (fun a => |Z a|^(2*k)) ≤ L^(2*k))
    (ha : ((6*(2*k:ℕ):ℝ)*L)^2 * (2^s*∏j∈Finset.range b,T (j+1):ℕ) < 1) :
    (P.product (Fintype.card (WindowLeaf T (b+1)))).evenMomentSq
      (multilinear (degreeTail (averagedCoefficient R
        (fun ω => windowFinType T s (X ω) (b+1) τ)) r₀) Z) k ≤
      (((6*(2*k:ℕ):ℝ)*L)^2*(2^s*∏j∈Finset.range b,T (j+1):ℕ))^r₀/
        (1-((6*(2*k:ℕ):ℝ)*L)^2*(2^s*∏j∈Finset.range b,T (j+1):ℕ)) := by
  apply (multilinear_moment_sq_scaled P Z k hk hcenter hL hMoment _ _).trans
  apply averaged_sparse_tail_energy R _ _ r₀ (by positivity) ha
  intro ω
  rw [windowFinType_degree]
  exact windowMinusCount_bound T s (X ω) b [] τ

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

def selectedChildren {α β : Type*} [DecidableEq α] (S : Finset (α × β)) : Finset α :=
  S.image Prod.fst

def selectedChildLeaves {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (h : α) : Finset β :=
  (S.filter (fun v => v.1=h)).image Prod.snd

@[to_additive]
theorem selected_prod_children {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [CommMonoid M] (S : Finset (α × β)) (f : α × β → M) :
    (∏h∈selectedChildren S, ∏v∈selectedChildLeaves S h, f (h,v)) = ∏v∈S, f v := by
  have he (h : α) : (∏v∈selectedChildLeaves S h, f (h,v)) =
      ∏v∈S.filter (fun v => v.1=h), f v := by
    unfold selectedChildLeaves
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro v hv
      rw [←(Finset.mem_filter.mp hv).2]
    · intro v hv w hw h
      apply Prod.ext
      · exact (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
      · exact h
  simp_rw [he]
  exact Finset.prod_fiberwise_of_maps_to (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) f

@[to_additive]
theorem selected_prod_index {α M : Type*} [DecidableEq α] [CommMonoid M]
    (S : Finset α) (f : α → M) :
    (∏i : Fin S.card, f (S.equivFin.symm i).val) = ∏v∈S, f v := by
  have h := Equiv.prod_comp S.equivFin.symm (fun v : S => f v.val)
  simpa only [Finset.prod_coe_sort] using h

/-- Occupied shape of an actual subset of a complete window tree. Only
occupied children are enumerated, so its leaves are exactly the selected
monomial variables, not the other complete-tree leaves. -/
def occupiedWindowShape (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → (path : List ℕ) → Finset (WindowLeaf T (b+1)) → CoefficientShape b
  | 0, path, S => .bottom S.card
      (fun i => motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X path))
      (fun i => (prouhetSeries s).coeff (((S.equivFin.symm i).val.1.val:ℤ)-X path))
  | b+1, path, S => .node (selectedChildren S).card
      (fun i => motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X path))
      (fun i => (prouhetSeries s).coeff ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X path))
      (fun i => occupiedWindowShape T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))

theorem occupiedWindowShape_admissible (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    (occupiedWindowShape T s X b path S).Admissible := by
  induction b generalizing path with
  | zero => exact fun _ => prouhet_motif_value s _
  | succ b ih => exact ⟨fun _ => prouhet_motif_value s _, fun _ => ih _ _⟩

/-- The literal coefficient product equals the evaluation of its occupied
shape; this is before any averaging or parity cancellation. -/
theorem occupiedWindowShape_eval (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) (τ : ℝ) :
    (occupiedWindowShape T s X b path S).eval τ =
      ∏v∈S, (1-windowLeafSign T s X (b+1) path τ v)/2 := by
  induction b generalizing path τ with
  | zero =>
    change (∏i : Fin S.card, _) = _
    refine (selected_prod_index S (fun v : Fin (T 0) × Fin 1 =>
      (motifIndicator s ((v.1.val:ℤ)-X path) -
        (prouhetSeries s).coeff ((v.1.val:ℤ)-X path)*τ)/2)).trans ?_
    apply Finset.prod_congr rfl
    intro v hv
    simp only [windowLeafSign,motifChildSign]
    ring
  | succ b ih =>
    change (∏i : Fin (selectedChildren S).card, _) = _
    simp_rw [ih]
    refine (selected_prod_index (selectedChildren S) (fun h : Fin (T (b+1)) =>
      ∏v∈selectedChildLeaves S h,
        (1-windowLeafSign T s X (b+1) (path++[h.val])
          (motifChildSign s (X path) h.val τ) v)/2)).trans ?_
    exact selected_prod_children S (fun v =>
      (1-windowLeafSign T s X (b+1+1) path τ v)/2)

theorem selected_children_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) :
    (∑h∈selectedChildren S, (selectedChildLeaves S h).card) = S.card := by
  simpa only [Finset.sum_const,smul_eq_mul,mul_one] using
    selected_sum_children S (fun _ => (1:ℕ))

theorem selectedChildLeaves_nonempty {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset (α × β)) (h : α) (hh : h∈selectedChildren S) :
    (selectedChildLeaves S h).Nonempty := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hh
  exact ⟨v.2,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩,rfl⟩⟩

theorem occupiedWindowShape_leafCount (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : (occupiedWindowShape T s X b path S).Choice) :
    ((occupiedWindowShape T s X b path S).termTree a).leafCount = S.card := by
  induction b generalizing path with
  | zero => simp [occupiedWindowShape,CoefficientShape.termTree,OccupiedParityTree.leafCount]
  | succ b ih =>
    change (∑i : Fin (selectedChildren S).card, _) = _
    simp_rw [ih]
    exact (selected_sum_index (selectedChildren S) (fun h =>
      (selectedChildLeaves S h).card)).trans (selected_children_card S)

theorem occupiedWindowShape_occupied (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) (hS : S.Nonempty)
    (a : (occupiedWindowShape T s X b path S).Choice) :
    ((occupiedWindowShape T s X b path S).termTree a).occupied := by
  induction b generalizing path with
  | zero => exact ⟨hS.card_pos,fun _ => trivial⟩
  | succ b ih =>
    refine ⟨(Finset.image_nonempty.mpr hS).card_pos,fun i => ?_⟩
    exact ih _ _ (selectedChildLeaves_nonempty S _
      ((selectedChildren S).equivFin.symm i).property) (a.1 i)

/-- Forced-leaf count for a term of an actual selected monomial. -/
theorem occupiedWindowShape_forced_count (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : (occupiedWindowShape T s X b path S).Choice)
    (hw : (occupiedWindowShape T s X b path S).weight a ≠ 0)
    (ho : ((occupiedWindowShape T s X b path S).termTree a).isOdd)
    (hn : ((occupiedWindowShape T s X b path S).termTree a).noSingleton) :
    2^(b+1) ≤ S.card := by
  simpa only [occupiedWindowShape_leafCount] using
    (occupiedWindowShape T s X b path S).surviving_leaves a hw ho hn

/-- The role choices depend only on the selected subset, not on any hidden
orientation. This common index type permits averaging before norm estimates. -/
def OccupiedWindowChoice (T : ℕ → ℕ) :
    (b : ℕ) → Finset (WindowLeaf T (b+1)) → Type
  | 0, S => Fin S.card → Fin 3
  | b+1, S =>
      ((i : Fin (selectedChildren S).card) → OccupiedWindowChoice T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)) ×
      (Fin (selectedChildren S).card → Fin 3)

noncomputable instance occupiedWindowChoiceFintype (T : ℕ → ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) → Fintype (OccupiedWindowChoice T b S)
  | 0, S => by unfold OccupiedWindowChoice; infer_instance
  | b+1, S => by
      letI := fun i : Fin (selectedChildren S).card =>
        occupiedWindowChoiceFintype T b
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
      unfold OccupiedWindowChoice
      infer_instance

noncomputable def occupiedWindowChoiceEquiv (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ) :
    (b : ℕ) → (path : List ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S ≃ (occupiedWindowShape T s X b path S).Choice
  | 0, _, _ => Equiv.refl _
  | b+1, path, S => Equiv.prodCongr
      (Equiv.piCongrRight fun i => occupiedWindowChoiceEquiv T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))
      (Equiv.refl _)

/-- The parity tree of a role choice is independent of all displacement bits. -/
noncomputable def occupiedWindowTerm (T : ℕ → ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S → OccupiedParityTree (b+1)
  | 0, S, a => .node S.card (fun _ => .leaf) a
  | b+1, S, a => .node (selectedChildren S).card
      (fun i => occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)) a.2

 theorem occupiedWindowTerm_eq (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) :
    (occupiedWindowShape T s X b path S).termTree
      (occupiedWindowChoiceEquiv T s X b path S a) = occupiedWindowTerm T b S a := by
  induction b generalizing path with
  | zero => rfl
  | succ b ih =>
    change OccupiedParityTree.node _ (fun i => _) _ = OccupiedParityTree.node _ _ _
    congr 1
    funext i
    exact ih _ _ _

noncomputable def occupiedWindowWeight (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) : ℝ :=
  (occupiedWindowShape T s X b path S).weight
    (occupiedWindowChoiceEquiv T s X b path S a)

/-- Exact source parity formula for the actual selected leaves, using a
single role index independent of the latent map. No fit conditioning. -/
theorem occupiedWindow_difference (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    (∏v∈S, (1-windowLeafSign T s X (b+1) path 1 v)/2) -
      (∏v∈S, (1-windowLeafSign T s X (b+1) path (-1) v)/2) =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then occupiedWindowWeight T s X b path S a else 0 := by
  rw [←occupiedWindowShape_eval,←occupiedWindowShape_eval,
    CoefficientShape.difference_expansion _ (occupiedWindowShape_admissible T s X b path S)]
  congr 1
  rw [←(occupiedWindowChoiceEquiv T s X b path S).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [occupiedWindowTerm_eq]
  rfl

/-- Averaging the complete exact expansion keeps all correlations of the
common hidden map. The indicator of an odd root is deterministic. -/
theorem occupiedWindow_averaged_difference {Ω : Type*} [Fintype Ω]
    (R : FiniteLaw Ω) (T : ℕ → ℕ) (s : ℕ) (X : Ω → List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1))) :
    R.expect (fun ω => ∏v∈S, (1-windowLeafSign T s (X ω) (b+1) path 1 v)/2) -
      R.expect (fun ω => ∏v∈S, (1-windowLeafSign T s (X ω) (b+1) path (-1) v)/2) =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then
          R.expect (fun ω => occupiedWindowWeight T s (X ω) b path S a) else 0 := by
  unfold expect
  rw [←Finset.sum_sub_distrib]
  simp_rw [←mul_sub,occupiedWindow_difference,mul_left_comm (R.mass _) 2,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [←Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (occupiedWindowTerm T b S a).isOdd <;> simp [h]

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Arbitrary functions of the actual posterior count have the translated
fair-binomial law, not only its generating polynomial. -/
theorem posterior_count_average {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑ b : ι → Bool, (∏i, (flagPosterior (d i)).mass (b i)) *
      F (∑i, (bitIndex (b i):ℤ))) =
    ∑k∈Finset.range ((∑i, hiddenTrial (d i))+1),
      fairBinomial (∑i, hiddenTrial (d i)) k * F ((∑i,(visibleOnes (d i):ℤ))+k) := by
  have H := congrArg (fun p : IntSeries => Finsupp.linearCombination ℝ F p.coeff)
    (posterior_count_series d)
  rw [fairSeries_sum,Finset.mul_sum] at H
  simp only [AddMonoidAlgebra.single_mul_single,one_mul,
    AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H

theorem fairBinomial_reflect (n k : ℕ) (hk : k ≤ n) :
    fairBinomial n (n-k) = fairBinomial n k := by
  simp only [fairBinomial,Nat.choose_symm hk]

/-- Reflection of the remaining hidden count. The known visible contribution
is kept, and no positivity assumption on the metadata mass is needed. -/
theorem posterior_count_average_reflected {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑ b : ι → Bool, (∏i, (flagPosterior (d i)).mass (b i)) *
      F (∑i, (bitIndex (b i):ℤ))) =
    ∑k∈Finset.range ((∑i, hiddenTrial (d i))+1),
      fairBinomial (∑i, hiddenTrial (d i)) k *
        F ((∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i))-k) := by
  rw [posterior_count_average]
  rw [←Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ ∑i,hiddenTrial (d i) := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  simp only [Nat.add_sub_cancel,fairBinomial_reflect _ _ hk',Nat.cast_sub hk']
  congr 2
  ring

/-- The actual local signed motif averaged over posterior orientations is
exactly a translated smoothed Prouhet polynomial. -/
theorem posterior_signed_motif {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      (prouhetSeries s).coeff (z+∑i,(bitIndex (b i):ℤ))) =
      (prouhetSeries s * fairSeries (∑i,hiddenTrial (d i))).coeff
        (z+(∑i,(visibleOnes (d i):ℤ))+(∑i,hiddenTrial (d i))) := by
  rw [posterior_count_average_reflected d (fun a => (prouhetSeries s).coeff (z+a)),
    fairSeries_sum,Finset.mul_sum,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [AddMonoidAlgebra.coeff_mul_single_apply]
  simp only [mul_comm]
  congr 2
  omega

/-- Singleton smoothing for literal hidden orientation bits. Other mechanisms
can now be conditioned on without changing this bound. -/
theorem posterior_signed_motif_bound {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    |∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      (prouhetSeries s).coeff (z+∑i,(bitIndex (b i):ℤ))| ≤
      (2:ℝ)^(s*s)*((2*binomialBound ((∑i,hiddenTrial (d i))/(s+1)))^s *
        binomialBound ((∑i,hiddenTrial (d i))/(s+1))) := by
  rw [posterior_signed_motif]
  exact (signed_binomial_smoothing _ s).1 _

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The literal unsigned window evaluated at an affine fair-binomial shift. -/
theorem windowKernel_binomial (n L : ℕ) (z : ℤ) :
    windowKernel n L z =
      ∑k∈Finset.range (n+1), fairBinomial n k *
        (if 0 ≤ z+(k:ℤ) ∧ z+(k:ℤ)<L then (1:ℝ) else 0) := by
  unfold windowKernel
  simp_rw [fairSeries_sum,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [←geomSeries_coeff,geomSeries]
  simp only [AddMonoidAlgebra.single_pow,one_pow,nsmul_eq_mul,mul_one,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single,Finsupp.single_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : (a:ℤ)=z+k
  · have h' : (k:ℤ)=(a:ℤ)-z := by omega
    simp only [ite_eq_left h,ite_eq_left h',mul_one]
  · have h' : (k:ℤ)≠(a:ℤ)-z := by omega
    simp only [ite_eq_right h,ite_eq_right h',mul_zero]

/-- Exact local anchor kernel for the actual posterior bits, with the known
visible contribution retained as a translation. -/
theorem posterior_unsigned_motif {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (s : ℕ) (z : ℤ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i)) *
      motifIndicator s (z+∑i,(bitIndex (b i):ℤ))) =
      windowKernel (∑i,hiddenTrial (d i)) (2^s) (z+∑i,(visibleOnes (d i):ℤ)) := by
  rw [posterior_count_average d (fun a => motifIndicator s (z+a)),windowKernel_binomial]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [motifIndicator,add_assoc]

/-- The finite-series functional form of the posterior count identity. -/
theorem posterior_count_support {ι : Type*} [Fintype ι]
    (d : ι → Option Bool) (F : ℤ → ℝ) :
    (∑b : ι → Bool, (∏i,(flagPosterior (d i)).mass (b i))*F (∑i,(bitIndex (b i):ℤ))) =
    ∑v∈(fairSeries (∑i,hiddenTrial (d i))).coeff.support,
      (fairSeries (∑i,hiddenTrial (d i))).coeff v * F ((∑i,(visibleOnes (d i):ℤ))+v) := by
  rw [posterior_count_average]
  have H := congrArg (fun p : IntSeries =>
    Finsupp.linearCombination ℝ (fun v => F ((∑i,(visibleOnes (d i):ℤ))+v)) p.coeff)
    (fairSeries_sum (∑i,hiddenTrial (d i)))
  simp only [AddMonoidAlgebra.coeff_sum,AddMonoidAlgebra.coeff_single,map_sum,
    Finsupp.linearCombination_single,smul_eq_mul] at H
  exact H.symm

/-- The actual two-sibling anchor multiplier. Global bits are shared by the
two siblings until AFTER averaging; their local bits are independent. -/
def posteriorJointAnchors {ιg ι₁ ι₂ : Type*} [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (z₁ z₂ : ℤ) : ℝ :=
  ∑bg : ιg → Bool, (∏i,(flagPosterior (dg i)).mass (bg i)) *
    (∑b₁ : ι₁ → Bool, (∏i,(flagPosterior (d₁ i)).mass (b₁ i)) *
      motifIndicator s (z₁+(∑i,(bitIndex (bg i):ℤ))+(∑i,(bitIndex (b₁ i):ℤ)))) *
    (∑b₂ : ι₂ → Bool, (∏i,(flagPosterior (d₂ i)).mass (b₂ i)) *
      motifIndicator s (z₂+(∑i,(bitIndex (bg i):ℤ))+(∑i,(bitIndex (b₂ i):ℤ))))

theorem posteriorJointAnchors_eq {ιg ι₁ ι₂ : Type*} [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (z₁ z₂ : ℤ) :
    posteriorJointAnchors dg d₁ d₂ s z₁ z₂ =
    jointWindowKernel (∑i,hiddenTrial (dg i)) (∑i,hiddenTrial (d₁ i))
      (∑i,hiddenTrial (d₂ i)) (2^s)
      (z₁+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₁ i):ℤ)))
      (z₂+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₂ i):ℤ))) := by
  unfold posteriorJointAnchors
  simp_rw [posterior_unsigned_motif,mul_assoc]
  rw [posterior_count_support dg (fun v =>
    windowKernel (∑i,hiddenTrial (d₁ i)) (2^s) (z₁+v+∑i,(visibleOnes (d₁ i):ℤ)) *
    windowKernel (∑i,hiddenTrial (d₂ i)) (2^s) (z₂+v+∑i,(visibleOnes (d₂ i):ℤ)))]
  unfold jointWindowKernel
  apply Finset.sum_congr rfl
  intro v hv
  have h₁ : z₁+((∑i,(visibleOnes (dg i):ℤ))+v)+(∑i,(visibleOnes (d₁ i):ℤ)) =
      z₁+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₁ i):ℤ))+v := by ring
  have h₂ : z₂+((∑i,(visibleOnes (dg i):ℤ))+v)+(∑i,(visibleOnes (d₂ i):ℤ)) =
      z₂+(∑i,(visibleOnes (dg i):ℤ))+(∑i,(visibleOnes (d₂ i):ℤ))+v := by ring
  rw [h₁,h₂,mul_assoc]

/-- Quantitative sibling summation now directly bounds genuine posterior
bits, not an independent-anchor surrogate. -/
theorem posterior_sibling_anchor_energy {ιg ι₁ ι₂ : Type*}
    [Fintype ιg] [Fintype ι₁] [Fintype ι₂]
    (dg : ιg → Option Bool) (d₁ : ι₁ → Option Bool) (d₂ : ι₂ → Option Bool)
    (s : ℕ) (A B C D : Finset ℤ) (c₁ c₂ : ℤ) :
    (∑a∈A, ∑b∈B, ∑_c∈closeLabels C (2^s) a, ∑_d∈closeLabels D (2^s) b,
      (posteriorJointAnchors dg d₁ d₂ s (a-c₁) (b-c₂))^2) ≤
    4*((2^s:ℕ):ℝ)^6*binomialBound (∑i,hiddenTrial (dg i))*
      binomialBound (∑i,hiddenTrial (d₂ i)) := by
  simp_rw [posteriorJointAnchors_eq]
  have he : ∀a c u v : ℤ, a-c+u+v = a-(c-u-v) := by intros; omega
  simp_rw [he]
  exact sibling_anchor_energy (∑i,hiddenTrial (dg i)) (∑i,hiddenTrial (d₁ i))
    (∑i,hiddenTrial (d₂ i)) (2^s) A B C D
    (c₁-(∑i,(visibleOnes (dg i):ℤ))-(∑i,(visibleOnes (d₁ i):ℤ)))
    (c₂-(∑i,(visibleOnes (dg i):ℤ))-(∑i,(visibleOnes (d₂ i):ℤ)))

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expect_mul_const (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => f a*c) = P.expect f*c := by
  unfold expect
  simp only [←mul_assoc,Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    P.expect (fun a => c*f a) = c*P.expect f := by
  unfold expect
  simp only [mul_left_comm (P.mass _) c,Finset.mul_sum]

theorem coordinateProduct_expect_product {n : ℕ} (P : Fin n → FiniteLaw α)
    (f : Fin n → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i,f i (x i)) = ∏i,(P i).expect (f i) := by
  unfold expect coordinateProduct
  simp only [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : Fin n) (a : α) => (P i).mass a*f i a)).symm

theorem expect_prod_split (P : FiniteLaw α) (Q : FiniteLaw β)
    (f : α → ℝ) (g : β → ℝ) :
    (P.prod Q).expect (fun x => f x.1*g x.2) = P.expect f * Q.expect g := by
  rw [expect_prod]
  simp_rw [expect_const_mul]
  exact expect_mul_const P f _

end FiniteLaw

/-- All local and global orientation collections on the complete index tree,
including unoccupied vertices and paths which do not fit. The type is fixed
before any selected monomial or role choices. `n` is the local trial count,
`g` the number of global paired trials, and T the full window counts. -/
def WindowAssignments (T n g : ℕ → ℕ) (A : Type) : ℕ → Type
  | 0 => PUnit
  | b+1 => (Fin (n b) → A) × (Fin (g b) → A) ×
      (Fin (T b) → WindowAssignments T n g A b)

noncomputable instance windowAssignmentsFintype (T n g : ℕ → ℕ) (A : Type) [Fintype A] :
    (b : ℕ) → Fintype (WindowAssignments T n g A b)
  | 0 => inferInstanceAs (Fintype PUnit)
  | b+1 => by
      letI := windowAssignmentsFintype T n g A b
      exact inferInstanceAs (Fintype ((Fin (n b) → A) × (Fin (g b) → A) ×
        (Fin (T b) → WindowAssignments T n g A b)))

def posteriorArray {n : ℕ} (d : Fin n → Option Bool) : FiniteLaw (Fin n → Bool) :=
  coordinateProduct (fun i => flagPosterior (d i))

/-- Actual independent posterior orientations at exact non-leaf metadata.
The common global bits in a group are drawn only once. -/
def windowPosteriorLaw (T n g : ℕ → ℕ) : (b : ℕ) →
    WindowAssignments T n g (Option Bool) b → FiniteLaw (WindowAssignments T n g Bool b)
  | 0, _ => ⟨fun _ => 1,fun _ => by norm_num,by change (∑_ : PUnit,(1:ℝ))=1; simp⟩
  | b+1, d => (posteriorArray d.1).prod ((posteriorArray d.2.1).prod
      (coordinateProduct (fun i => windowPosteriorLaw T n g b (d.2.2 i))))

/-- Displacements from the jointly generated bit tree. The ancestor global
map may vary off its plateau. No independent jitter per child is introduced.
The fixed center includes the deterministic half-trial corrections. -/
def sourceTreeAnchors (T n g : ℕ → ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → List ℕ → ℤ
  | 0, _, _, _ => 0
  | b+1, bits, incoming, [] => center b - (∑i,(bitIndex (bits.1 i):ℤ))-incoming
  | b+1, bits, _, h::tail => if hh : h<T b then
      sourceTreeAnchors T n g center globalShift b (bits.2.2 ⟨h,hh⟩)
        (globalShift b bits.2.1 ⟨h,hh⟩) tail else 0

theorem sourceTreeAnchors_root (T n g : ℕ → ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ) :
    sourceTreeAnchors T n g center globalShift (b+1) bits incoming [] =
      center b - (∑i,(bitIndex (bits.1 i):ℤ))-incoming := rfl

theorem sourceTreeAnchors_child (T n g : ℕ → ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (h : Fin (T b)) (tail : List ℕ) :
    sourceTreeAnchors T n g center globalShift (b+1) bits incoming (h.val::tail) =
      sourceTreeAnchors T n g center globalShift b (bits.2.2 h)
        (globalShift b bits.2.1 h) tail := by
  simp only [sourceTreeAnchors,dite_eq_left h.isLt]

/-- Moving the origin of a subtree preserves the literal type recursion. -/
theorem windowLeafSign_prefix (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (pre path : List ℕ) (τ : ℝ) (v : WindowLeaf T b) :
    windowLeafSign T s X b (pre++path) τ v =
      windowLeafSign T s (fun tail => X (pre++tail)) b path τ v := by
  induction b generalizing path τ with
  | zero => rfl
  | succ b ih =>
    change windowLeafSign T s X b _ _ v.2 = _
    rw [List.append_assoc,ih]
    rfl

/-- Exact recursive leaf signs for the complete bit tree, with one joint
parent-global shift supplied to each sibling's local mechanism. -/
def sourceTreeLeafSign (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → ℝ → WindowLeaf T b → ℝ
  | 0, _, _, τ, _ => τ
  | b+1, bits, incoming, τ, v =>
      sourceTreeLeafSign T n g s center globalShift b (bits.2.2 v.1)
        (globalShift b bits.2.1 v.1)
        (motifChildSign s (center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) v.1.val τ) v.2

theorem sourceTreeLeafSign_eq (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool b) (incoming : ℤ)
    (τ : ℝ) (v : WindowLeaf T b) :
    sourceTreeLeafSign T n g s center globalShift b bits incoming τ v =
      windowLeafSign T s (sourceTreeAnchors T n g center globalShift b bits incoming) b [] τ v := by
  induction b generalizing incoming τ with
  | zero => rfl
  | succ b ih =>
    change sourceTreeLeafSign T n g s center globalShift b _ _ _ v.2 =
      windowLeafSign T s _ b [v.1.val] _ v.2
    rw [ih]
    have hp := windowLeafSign_prefix T s
      (sourceTreeAnchors T n g center globalShift (b+1) bits incoming)
      b [v.1.val] []
      (motifChildSign s (center b-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) v.1.val τ) v.2
    simp only [List.append_nil,List.singleton_append,sourceTreeAnchors_child] at hp
    exact hp.symm

end TraceReconstruction

-- Actual subtree coefficient factorization and singleton cancellation.
noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- The factor at the current vertex of a fixed actual occupied role choice.
It only uses that vertex's displacement, never any descendant mechanism. -/
def occupiedRootWeight (T : ℕ → ℕ) (s : ℕ) :
    (b : ℕ) → (S : Finset (WindowLeaf T (b+1))) →
      OccupiedWindowChoice T b S → ℤ → ℝ
  | 0, S, a, X => ∏i : Fin S.card,
      bottomRoleWeight (motifIndicator s (((S.equivFin.symm i).val.1.val:ℤ)-X))
        ((prouhetSeries s).coeff (((S.equivFin.symm i).val.1.val:ℤ)-X)) (a i)
  | b+1, S, a, X => ∏i : Fin (selectedChildren S).card,
      @internalRoleWeight (occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)).isOdd
        (Classical.propDecidable _)
        (motifIndicator s ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X))
        ((prouhetSeries s).coeff ((((selectedChildren S).equivFin.symm i).val.val:ℤ)-X)) (a.2 i)

theorem occupiedWindowWeight_zero (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (path : List ℕ) (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) :
    occupiedWindowWeight T s X 0 path S a = occupiedRootWeight T s 0 S a (X path) := rfl

theorem occupiedWindowWeight_succ (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1+1)))
    (a : OccupiedWindowChoice T (b+1) S) :
    occupiedWindowWeight T s X (b+1) path S a =
      occupiedRootWeight T s (b+1) S a (X path) *
        ∏i : Fin (selectedChildren S).card,
          occupiedWindowWeight T s X b
            (path++[((selectedChildren S).equivFin.symm i).val.val])
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i) := by
  unfold occupiedWindowWeight
  change (∏i, _ * @internalRoleWeight
    ((occupiedWindowShape T s X b
      (path++[((selectedChildren S).equivFin.symm i).val.val])
      (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)).termTree
      (occupiedWindowChoiceEquiv T s X b
        (path++[((selectedChildren S).equivFin.symm i).val.val])
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))).isOdd
        (Classical.propDecidable _) _ _ _) = _
  simp_rw [occupiedWindowTerm_eq]
  rw [Finset.prod_mul_distrib,mul_comm]
  rfl

/-- Moving a subtree's path origin does not change any of its role factors. -/
theorem occupiedWindowWeight_prefix (T : ℕ → ℕ) (s : ℕ) (X : List ℕ → ℤ)
    (b : ℕ) (pre path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) :
    occupiedWindowWeight T s X b (pre++path) S a =
      occupiedWindowWeight T s (fun tail => X (pre++tail)) b path S a := by
  induction b generalizing path with
  | zero => rfl
  | succ b ih =>
    rw [occupiedWindowWeight_succ,occupiedWindowWeight_succ]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [List.append_assoc,ih]

theorem bottomRoleWeight_abs_le_one (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |bottomRoleWeight χ σ a| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> norm_num [bottomRoleWeight]

theorem internalRoleWeight_abs_le_one (odd : Prop) [Decidable odd]
    (χ σ : ℝ) (h : IsMotifValue χ σ) (a : Fin 3) :
    |internalRoleWeight odd χ σ a| ≤ 1 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl|rfl⟩ <;>
    fin_cases a <;> by_cases ho : odd <;> norm_num [internalRoleWeight,roleWeight,ho]

theorem occupiedRootWeight_abs_le_one (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) (X : ℤ) :
    |occupiedRootWeight T s b S a X| ≤ 1 := by
  cases b with
  | zero =>
    rw [occupiedRootWeight,Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun i _ => bottomRoleWeight_abs_le_one _ _ (prouhet_motif_value s _) (a i))
  | succ b =>
    rw [occupiedRootWeight,Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      (fun i _ => internalRoleWeight_abs_le_one _ _ _ (prouhet_motif_value s _) (a.2 i))

theorem occupiedWindowWeight_abs_le_one (T : ℕ → ℕ) (s : ℕ)
    (X : List ℕ → ℤ) (b : ℕ) (path : List ℕ) (S : Finset (WindowLeaf T (b+1)))
    (a : OccupiedWindowChoice T b S) : |occupiedWindowWeight T s X b path S a| ≤ 1 := by
  induction b generalizing path with
  | zero => exact occupiedRootWeight_abs_le_one T s 0 S a _
  | succ b ih =>
    rw [occupiedWindowWeight_succ,abs_mul,Finset.abs_prod]
    exact (mul_le_of_le_one_left (by positivity)
      (occupiedRootWeight_abs_le_one T s (b+1) S a _)).trans
      (Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun i _ => ih _ _ _))

/-- A singleton signed role factors off its signed motif with a scalar
independent of all displacements. Bottom zero-role terms really vanish. -/
theorem bottom_singleton_factor {n : ℕ} (a : Fin n → Fin 3) (i : Fin n)
    (hi : a i=2) (hrest : ∀j,j≠i → a j=0) :
    ∃c : ℝ, |c|≤1 ∧ ∀χ σ : Fin n → ℝ,
      (∏j,bottomRoleWeight (χ j) (σ j) (a j)) = c*σ i := by
  let c : ℝ := -(∏j∈Finset.univ.erase i,(0:ℝ))/2
  refine ⟨c,?_,?_⟩
  · have hp : 0 ≤ ∏j∈Finset.univ.erase i,(0:ℝ) := Finset.prod_nonneg (fun _ _ => le_rfl)
    have hp' : (∏j∈Finset.univ.erase i,(0:ℝ)) ≤ 1 := Finset.prod_le_one₀
      (fun _ _ => le_rfl) (fun _ _ => by norm_num)
    dsimp [c]
    rw [abs_div,abs_neg,abs_of_nonneg hp]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  · intro χ σ
    rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have he : (∏j∈Finset.univ.erase i,bottomRoleWeight (χ j) (σ j) (a j)) =
        ∏j∈Finset.univ.erase i,(0:ℝ) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [hrest j (Finset.mem_erase.mp hj).1,bottomRoleWeight,↓reduceIte]
    rw [he,hi]
    simp only [bottomRoleWeight,show (2:Fin 3)≠0 by decide,
      show (2:Fin 3)≠1 by decide,↓reduceIte]
    dsimp [c]
    ring

theorem internal_singleton_factor {n : ℕ} (odd : Fin n → Prop)
    (a : Fin n → Fin 3) (i : Fin n) (hi : a i=2) (hrest : ∀j,j≠i → a j=0) :
    ∃c : ℝ, |c|≤1 ∧ ∀χ σ : Fin n → ℝ,
      (∏j,@internalRoleWeight (odd j) (Classical.propDecidable _) (χ j) (σ j) (a j)) = c*σ i := by
  refine ⟨if odd i then 1 else 0,?_,?_⟩
  · split_ifs <;> norm_num
  · intro χ σ
    rw [Finset.prod_eq_single i]
    · by_cases ho : odd i <;> simp [internalRoleWeight,roleWeight,hi,ho]
    · intro j hj hji
      by_cases ho : odd j <;> simp [internalRoleWeight,roleWeight,hrest j hji,ho]
    · simp

namespace FiniteLaw

/-- Unoccupied independent coordinates integrate to one. -/
theorem coordinateProduct_expect_subtype {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (S : Finset (Fin n)) (f : S → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i : S, f i (x i.val)) =
      ∏i : S, (P i.val).expect (f i) := by
  have scalar : ∀f : S → ℝ,
      (∏j : Fin n, if hj : j∈S then f ⟨j,hj⟩ else 1) = ∏i : S,f i := by
    intro f
    calc
      _ = ∏j∈S, if hj : j∈S then f ⟨j,hj⟩ else 1 :=
        (Finset.prod_subset S.subset_univ (fun j _ hj => dite_eq_right hj)).symm
      _ = ∏i : S, if hj : i.val∈S then f ⟨i.val,hj⟩ else 1 :=
        Finset.prod_subtype S (fun _ => Iff.rfl) _
      _ = _ := by simp only [dite_eq_left (Subtype.property _)]
  let F : Fin n → α → ℝ := fun j a => if hj : j∈S then f ⟨j,hj⟩ a else 1
  have hp : ∀x : Fin n → α, (∏j,F j (x j)) = ∏i : S,f i (x i.val) := by
    intro x
    exact scalar (fun i => f i (x i.val))
  rw [show (fun x : Fin n → α => ∏i : S,f i (x i.val)) = (fun x => ∏j,F j (x j)) by
    funext x; exact (hp x).symm]
  rw [coordinateProduct_expect_product]
  have he : ∀j, (P j).expect (F j) = if hj : j∈S then (P j).expect (f ⟨j,hj⟩) else 1 := by
    intro j
    by_cases hj : j∈S
    · simp only [F,dite_eq_left hj]
    · simp only [F,dite_eq_right hj,expect_const]
  simp_rw [he]
  exact scalar (fun i => (P i.val).expect (f i))

theorem coordinateProduct_expect_selected {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin n → FiniteLaw α) (S : Finset (Fin n)) (f : Fin S.card → α → ℝ) :
    (coordinateProduct P).expect (fun x => ∏i : Fin S.card, f i (x (S.equivFin.symm i).val)) =
      ∏i : Fin S.card, (P (S.equivFin.symm i).val).expect (f i) := by
  have hp : ∀x : Fin n → α,
      (∏i : Fin S.card,f i (x (S.equivFin.symm i).val)) =
        ∏i : S,f (S.equivFin i) (x i.val) := by
    intro x
    simpa only [Equiv.apply_symm_apply] using
      Equiv.prod_comp S.equivFin.symm (fun i : S => f (S.equivFin i) (x i.val))
  simp_rw [hp,coordinateProduct_expect_subtype]
  symm
  simpa only [Equiv.apply_symm_apply] using
    Equiv.prod_comp S.equivFin.symm (fun i : S => (P i.val).expect (f (S.equivFin i)))

theorem expect_prod_selected {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {n : ℕ} (P : FiniteLaw α) (Q : FiniteLaw β) (R : Fin n → FiniteLaw γ)
    (S : Finset (Fin n)) (f : α → ℝ) (h : β → Fin S.card → γ → ℝ) :
    (P.prod (Q.prod (coordinateProduct R))).expect (fun x =>
      f x.1 * ∏i : Fin S.card, h x.2.1 i (x.2.2 (S.equivFin.symm i).val)) =
      P.expect f * Q.expect (fun z => ∏i : Fin S.card,
        (R (S.equivFin.symm i).val).expect (h z i)) := by
  simp_rw [expect_prod,expect_const_mul,coordinateProduct_expect_selected]
  rw [expect_mul_const]

theorem abs_expect_le_const {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (c : ℝ) (h : ∀a, |f a|≤c) : |P.expect f|≤c :=
  (P.abs_expect_le f).trans ((P.expect_mono h).trans_eq (P.expect_const c))

end FiniteLaw


/-- A fixed real coefficient term evaluated on the actual complete bit tree.
The selected role choice is fixed independently of these bits. -/
def sourceRoleTerm (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) : ℝ :=
  occupiedWindowWeight T s (sourceTreeAnchors T n g center globalShift (b+1) bits incoming)
    b [] S a

def sourceRoleAverage (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) : ℝ :=
  (windowPosteriorLaw T n g (b+1) d).expect
    (fun bits => sourceRoleTerm T n g s center globalShift b bits incoming S a)

theorem sourceRoleTerm_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (bits : WindowAssignments T n g Bool 1) (incoming : ℤ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) :
    sourceRoleTerm T n g s center globalShift 0 bits incoming S a =
      occupiedRootWeight T s 0 S a (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) := rfl

theorem sourceRoleTerm_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) :
    sourceRoleTerm T n g s center globalShift (b+1) bits incoming S a =
      occupiedRootWeight T s (b+1) S a (center (b+1)-(∑i,(bitIndex (bits.1 i):ℤ))-incoming) *
        ∏i : Fin (selectedChildren S).card,
          sourceRoleTerm T n g s center globalShift b
            (bits.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) bits.2.1 ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i) := by
  unfold sourceRoleTerm
  rw [occupiedWindowWeight_succ]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hp := occupiedWindowWeight_prefix T s
    (sourceTreeAnchors T n g center globalShift (b+1+1) bits incoming) b
    [((selectedChildren S).equivFin.symm i).val.val] []
    (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)
  simpa only [List.append_nil,List.nil_append,List.singleton_append,sourceTreeAnchors_child] using hp

theorem sourceRoleAverage_zero (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (d : WindowAssignments T n g (Option Bool) 1) (incoming : ℤ)
    (S : Finset (WindowLeaf T 1)) (a : OccupiedWindowChoice T 0 S) :
    sourceRoleAverage T n g s center globalShift 0 d incoming S a =
      (posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s 0 S a (center 0-(∑i,(bitIndex (loc i):ℤ))-incoming)) := by
  rw [sourceRoleAverage]
  simp_rw [sourceRoleTerm_zero]
  rcases d with ⟨dl,dg,dc⟩
  change ((posteriorArray dl).prod ((posteriorArray dg).prod
    (coordinateProduct (fun i => windowPosteriorLaw T n g 0 (dc i))))).expect
      (fun bits => occupiedRootWeight T s 0 S a
        (center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)) = _
  rw [expect_prod]
  simp only [expect_const]

theorem sourceRoleAverage_succ (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1+1))) (a : OccupiedWindowChoice T (b+1) S) :
    sourceRoleAverage T n g s center globalShift (b+1) d incoming S a =
      (posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s (b+1) S a (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming)) *
      (posteriorArray d.2.1).expect (fun glob =>
        ∏i : Fin (selectedChildren S).card,
          sourceRoleAverage T n g s center globalShift b
            (d.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)) := by
  rw [sourceRoleAverage]
  simp_rw [sourceRoleTerm_succ]
  exact FiniteLaw.expect_prod_selected (posteriorArray d.1) (posteriorArray d.2.1)
    (fun i => windowPosteriorLaw T n g (b+1) (d.2.2 i)) (selectedChildren S)
    (fun loc => occupiedRootWeight T s (b+1) S a
      (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming))
    (fun glob i bits => sourceRoleTerm T n g s center globalShift b bits
      (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
      (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))

theorem sourceRoleAverage_abs_le_one (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤1 := by
  apply FiniteLaw.abs_expect_le_const
  intro bits
  exact occupiedWindowWeight_abs_le_one T s _ b [] S a

/-- The exact signed smoothing cost read off the visible metadata alone. -/
def posteriorSmoothingCost {ι : Type*} [Fintype ι] (s : ℕ) (d : ι → Option Bool) : ℝ :=
  (2:ℝ)^(s*s)*((2*binomialBound ((∑i,hiddenTrial (d i))/(s+1)))^s *
    binomialBound ((∑i,hiddenTrial (d i))/(s+1)))

/-- A purely numerical typical-metadata condition on every local collection.
It includes unoccupied vertices and is fixed before a coefficient is chosen. -/
def MetadataSmoothingCap (T n g : ℕ → ℕ) (s : ℕ) (η : ℝ) :
    (b : ℕ) → WindowAssignments T n g (Option Bool) b → Prop
  | 0, _ => True
  | b+1, d => posteriorSmoothingCost s d.1 ≤ η ∧
      ∀h, MetadataSmoothingCap T n g s η b (d.2.2 h)

def occupiedRootHasSingleton (T : ℕ → ℕ) : (b : ℕ) →
    (S : Finset (WindowLeaf T (b+1))) → OccupiedWindowChoice T b S → Prop
  | 0, _, a => ∃i, a i=2 ∧ ∀j,j≠i → a j=0
  | _+1, _, a => ∃i, a.2 i=2 ∧ ∀j,j≠i → a.2 j=0

theorem occupiedRoot_singleton_factor (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : occupiedRootHasSingleton T b S a) :
    ∃c : ℝ, |c|≤1 ∧ ∃label : ℤ, ∀X,
      occupiedRootWeight T s b S a X = c*(prouhetSeries s).coeff (label-X) := by
  cases b with
  | zero =>
    obtain ⟨i,hi,hr⟩ := h
    obtain ⟨c,hc,hfac⟩ := bottom_singleton_factor a i hi hr
    refine ⟨c,hc,((S.equivFin.symm i).val.1.val:ℤ),fun X => ?_⟩
    exact hfac _ _
  | succ b =>
    obtain ⟨i,hi,hr⟩ := h
    obtain ⟨c,hc,hfac⟩ := internal_singleton_factor
      (fun j => (occupiedWindowTerm T b
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val) (a.1 j)).isOdd)
      a.2 i hi hr
    refine ⟨c,hc,(((selectedChildren S).equivFin.symm i).val.val:ℤ),fun X => ?_⟩
    exact hfac _ _

theorem occupiedRoot_singleton_average (T : ℕ → ℕ) (s b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (h : occupiedRootHasSingleton T b S a) {m : ℕ} (d : Fin m → Option Bool)
    (center incoming : ℤ) :
    |(posteriorArray d).expect (fun loc => occupiedRootWeight T s b S a
      (center-(∑i,(bitIndex (loc i):ℤ))-incoming))| ≤ posteriorSmoothingCost s d := by
  obtain ⟨c,hc,label,hfac⟩ := occupiedRoot_singleton_factor T s b S a h
  simp_rw [hfac,expect_const_mul,abs_mul]
  have he : ∀loc : Fin m → Bool,
      label-(center-(∑i,(bitIndex (loc i):ℤ))-incoming) =
        (label-center+incoming)+(∑i,(bitIndex (loc i):ℤ)) := by intro loc; omega
  simp_rw [he]
  have hb : |(posteriorArray d).expect (fun loc =>
      (prouhetSeries s).coeff ((label-center+incoming)+(∑i,(bitIndex (loc i):ℤ))))| ≤
        posteriorSmoothingCost s d := by
    have hb := posterior_signed_motif_bound d s (label-center+incoming)
    unfold posteriorArray coordinateProduct expect posteriorSmoothingCost
    convert hb using 1
    congr 3
    exact Subsingleton.elim _ _
  calc
    _ ≤ 1*|(posteriorArray d).expect (fun loc =>
        (prouhetSeries s).coeff ((label-center+incoming)+(∑i,(bitIndex (loc i):ℤ))))| :=
      mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using hb

theorem abs_prod_le_coordinate {ι : Type*} [Fintype ι] (f : ι → ℝ) (i : ι)
    (h : ∀j,j≠i → |f j|≤1) : |∏j,f j|≤|f i| := by
  rw [Finset.abs_prod,←Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have he : (∏j∈Finset.univ.erase i,|f j|)≤1 :=
    Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun j hj => h j (Finset.mem_erase.mp hj).1)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right he (abs_nonneg (f i))

/-- Literal singleton cancellation for the complete posterior bit tree.
No successful-fit event is conditioned on, and the common parent-global
jitter is retained until after the child factors have averaged. -/
theorem sourceRoleAverage_singleton (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d)
    (hsing : ¬(occupiedWindowTerm T b S a).noSingleton) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤η := by
  induction b generalizing incoming with
  | zero =>
    have hh : Odd (signedRoleCount a) ∧ activeRoleCount a=1 := by
      by_contra! h
      apply hsing
      exact ⟨fun ho he => h ho he,fun _ => trivial⟩
    have hr : occupiedRootHasSingleton T 0 S a :=
      (odd_roles_singleton_or_branch a hh.1).resolve_right (by omega)
    rw [sourceRoleAverage_zero]
    exact (occupiedRoot_singleton_average T s 0 S a hr d.1 _ _).trans hcap.1
  | succ b ih =>
    rw [sourceRoleAverage_succ,abs_mul]
    have hroot : |(posteriorArray d.1).expect (fun loc =>
        occupiedRootWeight T s (b+1) S a
          (center (b+1)-(∑i,(bitIndex (loc i):ℤ))-incoming))|≤1 :=
      FiniteLaw.abs_expect_le_const _ _ 1 (fun _ => occupiedRootWeight_abs_le_one T s (b+1) S a _)
    have hglob : |(posteriorArray d.2.1).expect (fun glob =>
        ∏i : Fin (selectedChildren S).card,
          sourceRoleAverage T n g s center globalShift b
            (d.2.2 ((selectedChildren S).equivFin.symm i).val)
            (globalShift (b+1) glob ((selectedChildren S).equivFin.symm i).val)
            (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i))|≤1 := by
      apply FiniteLaw.abs_expect_le_const
      intro glob
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        (fun i _ => sourceRoleAverage_abs_le_one T n g s center globalShift b _ _ _ _)
    by_cases hr : occupiedRootHasSingleton T (b+1) S a
    · have hh := (occupiedRoot_singleton_average T s (b+1) S a hr d.1
        (center (b+1)) incoming).trans hcap.1
      exact (mul_le_mul_of_nonneg_left hglob (abs_nonneg _)).trans (by simpa using hh)
    · have hex : ∃i, ¬(occupiedWindowTerm T b
          (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val) (a.1 i)).noSingleton := by
        by_contra! h
        apply hsing
        refine ⟨?_,h⟩
        intro ho he
        have hh := odd_roles_singleton_or_branch a.2 ho
        exact hr (hh.resolve_right (by omega))
      obtain ⟨i,hi⟩ := hex
      have hsmall : |(posteriorArray d.2.1).expect (fun glob =>
          ∏j : Fin (selectedChildren S).card,
            sourceRoleAverage T n g s center globalShift b
              (d.2.2 ((selectedChildren S).equivFin.symm j).val)
              (globalShift (b+1) glob ((selectedChildren S).equivFin.symm j).val)
              (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val) (a.1 j))|≤η := by
        apply FiniteLaw.abs_expect_le_const
        intro glob
        apply (abs_prod_le_coordinate _ i (fun j _ =>
          sourceRoleAverage_abs_le_one T n g s center globalShift b _ _ _ _)).trans
        exact ih _ _ _ _ (hcap.2 _) hi
      exact (mul_le_mul_of_nonneg_right hroot (abs_nonneg _)).trans (by simpa using hsmall)

end TraceReconstruction

end
end
end
end
end
end
end
end

end OAI
