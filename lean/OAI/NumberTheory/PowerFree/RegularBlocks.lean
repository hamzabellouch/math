import OAI.NumberTheory.PowerFree.PrimeBlocks

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

theorem independent_many_regular {r : ℕ} {S : Type*} [Fintype S]
    {Ω : Fin r → Type*} [∀ i, Fintype (Ω i)]
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a = 1)
    (b : (∀ i, Ω i) → S → Fin r → ℝ)
    (hb : ∀ x z i, 0 ≤ b x z i) (η ξ : ℝ) (hξ : 0 < ξ)
    (hmean : ∀ z i x, (∑ a, w i a * b (Function.update x i a) z i) ≤ η) :
    ∃ x : ∀ i, Ω i,
      ((Finset.univ.filter fun z : S => ∀ i, b x z i ≤ ξ).card : ℝ) ≥
        (1 - (r : ℝ)*η/ξ) * Fintype.card S := by
  classical
  let W : (∀ i, Ω i) → ℝ := fun x => ∏ i, w i (x i)
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun i _ => hw i (x i)
  have hsumW : ∑ x, W x = 1 := by
    change (∑ x : ∀ i, Ω i, ∏ i, w i (x i)) = 1
    rw [← Fintype.prod_sum]
    simp only [hsum,Finset.prod_const_one]
  have hm (z : S) (i : Fin r) : ∑ x, W x * b x z i ≤ η :=
    independent_average_le w hw hsum i (fun x => b x z i) η (hmean z i)
  have hbad (z : S) :
      (∑ x, W x * if ∃ i, ξ < b x z i then (1 : ℝ) else 0) ≤ (r : ℝ)*η/ξ := by
    calc
      _ ≤ ∑ x, W x * ((∑ i, b x z i)/ξ) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
          (bad_blocks_indicator_le (b x z) (hb x z) ξ hξ) (hW x)
      _ = (∑ i, ∑ x, W x * b x z i)/ξ := by
        simp_rw [← mul_div_assoc,Finset.mul_sum]
        rw [← Finset.sum_div,Finset.sum_comm]
      _ ≤ (∑ _i : Fin r, η)/ξ := div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => hm z i) hξ.le
      _ = (r : ℝ)*η/ξ := by simp
  obtain ⟨x,hx⟩ := exists_many_regular W hW hsumW
    (fun x z => ∃ i, ξ < b x z i) ((r : ℝ)*η/ξ) hbad
  refine ⟨x,?_⟩
  simpa only [not_exists,not_lt] using hx

lemma adaptiveStates_precomp {K V σ α β : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) (f : β → α)
    (n i : ℕ) (s : σ) (a : β) :
    adaptiveStates (fun j t b => W j t (f b)) next n i s a =
      adaptiveStates W next n i s (f a) := by
  induction n generalizing i s with
  | zero => rfl
  | succ n ih => simp only [adaptiveStates,ih]

noncomputable def selectedBlocks {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, BlockSample (P i) (ell i) T) : Fin r → Finset ℕ :=
  fun i => blockSet (a i)

lemma selectedBlocks_update {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, BlockSample (P i) (ell i) T)
    (i : Fin r) (u : BlockSample (P i) (ell i) T) :
    selectedBlocks (Function.update a i u) = Function.update (selectedBlocks a) i (blockSet u) := by
  funext j
  by_cases h : j = i
  · subst j; simp [selectedBlocks]
  · simp [selectedBlocks,Function.update_of_ne h]

theorem regular_adaptive_blocks {K V σ S : Type*}
    [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype S]
    {r : ℕ} (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T n : ℕ)
    (W : S → ℕ → σ → (Fin r → Finset ℕ) → Submodule K V)
    (next : S → ℕ → σ → Submodule K V → σ) (start : S → σ)
    (minor : S → σ → ℤ)
    (hW : ∀ z j s B i A A', A ⊆ A' →
      W z j s (Function.update B i A) ≤ W z j s (Function.update B i A'))
    (X ζ B η ξ : ℝ) (hX : 1 < X) (hζ : 0 < ζ) (hξ : 0 < ξ)
    (hp : ∀ i p, p ∈ P i → p.Prime)
    (hsmall : ∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ))
    (hminor : ∀ z A, (∀ i, A i ⊆ P i) →
      ∀ t ∈ adaptiveStates (W z) (next z) n 0 (start z) A,
        minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B)
    (hT : 0 < T) (hsize : ∀ i, ell i+T < (P i).card)
    (hη : ∀ i, (((Module.finrank K V+1)^n : ℕ) : ℝ)/T +
      (⌊(B*(n+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) :
    ∃ A : Fin r → Finset ℕ,
      (∀ i, A i ⊆ P i ∧ ell i < (A i).card ∧ (A i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : S => ∀ i,
        ((∑ p ∈ A i,
          if (p : ℤ) ∣ ((adaptiveStates (W z) (next z) n 0 (start z) A).map (minor z)).prod
          then (1 : ℝ) else 0) / (A i).card) ≤ ξ).card : ℝ) ≥
          (1-(r : ℝ)*η/ξ)*Fintype.card S := by
  classical
  let Ω := fun i => BlockSample (P i) (ell i) T
  let w : ∀ i, Ω i → ℝ := fun i => blockWeight (P i) (ell i) T
  let M := fun z A => ((adaptiveStates (W z) (next z) n 0 (start z) A).map (minor z)).prod
  let b : (∀ i, Ω i) → S → Fin r → ℝ := fun a z i =>
    (∑ p ∈ selectedBlocks a i, if (p : ℤ) ∣ M z (selectedBlocks a) then (1 : ℝ) else 0) /
      (selectedBlocks a i).card
  have hb : ∀ a z i, 0 ≤ b a z i := by
    intro a z i
    exact div_nonneg (Finset.sum_nonneg fun p _ => by split_ifs <;> positivity)
      (Nat.cast_nonneg _)
  have hmean : ∀ z i a, (∑ u, w i u * b (Function.update a i u) z i) ≤ η := by
    intro z i a
    let A₀ := selectedBlocks a
    let Wi := fun j s A => W z j s (Function.update A₀ i A)
    let bad : Finset ℕ → Finset ℕ := fun A => (P i).filter fun p : ℕ =>
      (p : ℤ) ∣ M z (Function.update A₀ i A)
    have hm (A : Finset ℕ) (hA : A ⊆ P i) :
        ∀ t ∈ adaptiveStates Wi (next z) n 0 (start z) A,
          minor z t ≠ 0 ∧ |(minor z t : ℝ)| ≤ X^B := by
      rw [adaptiveStates_precomp]
      apply hminor z
      intro j
      by_cases h : j = i
      · subst j; simpa using hA
      · simpa only [Function.update_of_ne h, A₀, selectedBlocks] using (blockSet_spec (a j)).1
    have hdel := adaptive_deletion_bound Wi (next z)
      (fun j s A A' hAA' => hW z j s A₀ i A A' hAA') (minor z) n (start z)
      (P i) (hp i) X ζ B hX hζ (hsmall i) hm (ell i) T hT (hsize i)
    dsimp only at hdel
    simp only [Wi, adaptiveStates_precomp] at hdel
    change ((∑ j ∈ Finset.range T, badFraction (P i) (ell i+j+1) bad) / T) ≤ _ at hdel
    have heq : (∑ u, w i u * b (Function.update a i u) z i) =
        (∑ j ∈ Finset.range T, badFraction (P i) (ell i+j+1) bad) / T := by
      rw [← blockWeight_bad_average]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [w,b]
      rw [selectedBlocks_update, Function.update_self]
      congr 2
      apply Finset.sum_congr rfl
      intro p hpU
      have hpP := (blockSet_spec u).1 hpU
      simp only [bad,Finset.mem_filter,hpP,true_and,A₀]
    rw [heq]
    exact hdel.trans (hη i)
  obtain ⟨a,ha⟩ := independent_many_regular w
    (fun i => blockWeight_nonneg (P i) (ell i) T)
    (fun i => blockWeight_sum (P i) (ell i) T hT (hsize i).le)
    b hb η ξ hξ hmean
  refine ⟨selectedBlocks a,?_,ha⟩
  intro i
  obtain ⟨hsub,hcard⟩ := blockSet_spec (a i)
  refine ⟨hsub,?_,?_⟩
  · change ell i < (blockSet (a i)).card
    rw [hcard]; omega
  · change (blockSet (a i)).card ≤ ell i+T
    rw [hcard]
    have := (a i).1.isLt
    omega

open MvPolynomial

noncomputable def cumulativeBlockPrimes {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val ≤ i).biUnion B

theorem cumulativeBlockPrimes_mono {r : ℕ} {B C : Fin r → Finset ℕ}
    (hBC : ∀ j, B j ⊆ C j) (i : ℕ) :
    cumulativeBlockPrimes B i ⊆ cumulativeBlockPrimes C i := by
  classical
  intro p hp
  obtain ⟨j,hj,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨j,hj,hBC j hp⟩

def pathDegreeBudget (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => patchDegreeBudget n A h (kernelDegreeBudget (d i) h (pathDegreeBudget n d A h e i))

noncomputable def physicalKernel {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E) :=
  stagedEvaluationSpace (evaluationCell G.points s.1 z (cumulativeBlockPrimes B i)) (d i) E

noncomputable def physicalNext {n E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n :=
  firstCoveringChild z s (kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W)

def PhysicalState {n : ℕ} (G : KernelGeometry n) (h e : ℕ) (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) : Prop :=
  KernelParent h e s.1 ∧ s.2.On s.1 ∧ s.2.Bounded e G.height ∧ PatchPieceCovers s z

theorem physicalKernel_mono {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    {B C : Fin r → Finset ℕ} (hBC : ∀ j, B j ⊆ C j) :
    physicalKernel (E := E) G d z i s B ≤ physicalKernel G d z i s C :=
  stagedEvaluationSpace_mono (evaluationCell_antitone G.points s.1 z
    (cumulativeBlockPrimes_mono hBC i))

theorem physical_step {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : PhysicalState G h (pathDegreeBudget n d A h e i) z s)
    (B : Fin r → Finset ℕ) :
    let W := physicalKernel (E := E) G d z i s B
    let t := physicalNext G d A h e z i s W
    PhysicalState G h (pathDegreeBudget n d A h e (i+1)) z t ∧
      t ∈ kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W ∧
      s.1 ≤ t.1 ∧ stagedKernelPolynomials (d i) E W ⊆ t.1 ∧
      affineDimension t.1 ≤ affineDimension s.1 ∧
      (¬ stagedKernelPolynomials (d i) E W ⊆ s.1 → affineDimension t.1 < affineDimension s.1) := by
  classical
  dsimp only
  have hc := kernelChildList_spec G (d i) A h (pathDegreeBudget n d A h e i) s.1
    (physicalKernel (E := E) G d z i s B) hs.1
  have hzc : z ∈ evaluationCell G.points s.1 z (cumulativeBlockPrimes B i) := by
    exact Finset.mem_filter.mpr ⟨hz,hs.2.2.2.1,by simp⟩
  have hzF : ∀ p ∈ stagedKernelPolynomials (d i) E (physicalKernel G d z i s B),
      eval (fun l => (z l : ℂ)) p = 0 := by
    rintro p ⟨v,hv,rfl,_⟩
    exact hv.2 z hzc
  have hsel := firstCoveringChild_spec z s _ (hc.2.2 z hz hs.2.2.2.1 hzF)
  have hg := hc.2.1 _ hsel.1
  obtain ⟨⟨hp,hle,hdim,hdeg,hOn,hBound,_⟩,hF,hdim',hstrict⟩ := hg
  exact ⟨⟨⟨hp,hdim,hdeg⟩,hOn,hBound,hsel.2⟩,hsel.1,hle,hF,hdim',hstrict⟩

theorem physical_path_good {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (hz : z ∈ G.points)
    (B : Fin r → Finset ℕ) (m i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (hs : PhysicalState G h (pathDegreeBudget n d A h e i) z s) :
    ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s B,
      ∃ j, i ≤ j ∧ j ≤ i+m ∧ PhysicalState G h (pathDegreeBudget n d A h e j) z t := by
  induction m generalizing i s with
  | zero =>
    intro t ht
    have ht : t = s := by simpa only [adaptiveStates,List.mem_singleton] using ht
    subst t
    exact ⟨i,le_rfl,by omega,hs⟩
  | succ m ih =>
    intro t ht
    rcases List.mem_cons.mp ht with hts | ht
    · subst t
      exact ⟨i,le_rfl,by omega,hs⟩
    · have hstep := (physical_step (E := E) G d A h e z hz i s hs B).1
      obtain ⟨j,hij,hj,htj⟩ := ih (i+1) _ hstep t ht
      exact ⟨j,by omega,by omega,htj⟩

theorem physical_rank_mono_stable {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (m i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    {B C : Fin r → Finset ℕ} (hBC : ∀ j, B j ⊆ C j) :
    adaptiveCode (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s C ≤
      adaptiveCode (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s B ∧
    (adaptiveCode (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s C =
      adaptiveCode (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s B →
    adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s C =
      adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m i s B) := by
  let := totalSpace_finite (n := n) (K := ℂ) E
  exact adaptiveCode_mono_stable _ _ B C (fun i s => physicalKernel_mono G d z i s hBC) m i s

open MvPolynomial
open scoped BigOperators

theorem physical_uniform_minor_height (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
      ∀ (G : KernelGeometry n) (z : Fin n → ℤ), z ∈ G.points →
      ∀ (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
        PhysicalState G h e z s → ∀ (r : ℕ) (B : Fin r → Finset ℕ),
      ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z) (physicalNext G d A h e z) m 0 s B,
        eval z t.2.minor ≠ 0 ∧ |((eval z t.2.minor : ℤ) : ℝ)| ≤ C*G.height^b := by
  classical
  let D := (Finset.range (m+1)).sup (pathDegreeBudget n d A h e)
  obtain ⟨C,hC,b,hb⟩ := uniform_patch_minor_height n D
  refine ⟨C,hC,b,?_⟩
  intro G z hz s hs r B t ht
  obtain ⟨j,_,hj,hjt⟩ := physical_path_good (E := E) G d A h e z hz B m 0 s hs t ht
  have hD : pathDegreeBudget n d A h e j ≤ D :=
    Finset.le_sup (f := pathDegreeBudget n d A h e) (Finset.mem_range.mpr (by omega))
  exact ⟨hjt.2.2.2.2,hb t.2 G.height G.one_le_height (hjt.2.2.1.mono hD) z (G.bounded z hz)⟩

theorem physical_regular_blocks (n : ℕ) (d : ℕ → ℕ) (A h e m E : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ,
    ∀ (G : KernelGeometry n)
      (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n),
      (∀ z, PhysicalState G h e z.val (start z)) →
    ∀ (r : ℕ) (P : Fin r → Finset ℕ) (ell : Fin r → ℕ) (T : ℕ)
      (X ζ w η ξ : ℝ), 1 < X → C ≤ X → 0 ≤ w → G.height ≤ X^w → 0 < ζ → 0 < ξ →
      (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → X^ζ ≤ (p : ℝ)) →
      0 < T → (∀ i, ell i+T < (P i).card) →
      (∀ i, ((((E+n).choose n+1)^m : ℕ) : ℝ)/T +
        (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η) →
    ∃ B : Fin r → Finset ℕ,
      (∀ i, B i ⊆ P i ∧ ell i < (B i).card ∧ (B i).card ≤ ell i+T) ∧
      ((Finset.univ.filter fun z : G.points => ∀ i,
        ((∑ p ∈ B i,
          if (p : ℤ) ∣ ((adaptiveStates (physicalKernel (E := E) G d z.val)
            (physicalNext G d A h e z.val) m 0 (start z) B).map
            (fun t => eval z.val t.2.minor)).prod
          then (1 : ℝ) else 0) / (B i).card) ≤ ξ).card : ℝ) ≥
            (1-(r : ℝ)*η/ξ)*G.points.card := by
  classical
  obtain ⟨C,hC,b,hb⟩ := physical_uniform_minor_height n d A h e m E
  refine ⟨C,hC,b,?_⟩
  intro G start hs r P ell T X ζ w η ξ hX hCX hw hheight hζ hξ hp hsmall hT hsize hη
  let := totalSpace_finite (n := n) (K := ℂ) E
  have hmono : ∀ (z : G.points) j s (B : Fin r → Finset ℕ) i U U', U ⊆ U' →
      physicalKernel (E := E) G d z.val j s (Function.update B i U) ≤
      physicalKernel G d z.val j s (Function.update B i U') := by
    intro z j s B i U U' hUU'
    apply physicalKernel_mono
    intro k
    by_cases hk : k = i
    · subst k; simpa using hUU'
    · simp only [Function.update_of_ne hk]
      exact Finset.Subset.refl _
  have hminor : ∀ (z : G.points) B, (∀ i, B i ⊆ P i) →
      ∀ t ∈ adaptiveStates (physicalKernel (E := E) G d z.val)
          (physicalNext G d A h e z.val) m 0 (start z) B,
        eval z.val t.2.minor ≠ 0 ∧ |((eval z.val t.2.minor : ℤ) : ℝ)| ≤ X^(w*b+1) := by
    intro z B _ t ht
    have ht' := hb G z.val z.property (start z) (hs z) r B t ht
    refine ⟨ht'.1,ht'.2.trans ?_⟩
    calc
      C*G.height^b ≤ X*(X^w)^b := mul_le_mul hCX
        (pow_le_pow_left₀ (zero_le_one.trans G.one_le_height) hheight b)
        (pow_nonneg (zero_le_one.trans G.one_le_height) b) (zero_lt_one.trans hX).le
      _ = X^(w*b+1) := by
        rw [Real.rpow_add (zero_lt_one.trans hX), Real.rpow_one,
          Real.rpow_mul (zero_lt_one.trans hX).le,Real.rpow_natCast,mul_comm]
  have hη' : ∀ i, (((Module.finrank ℂ (totalSpace (σ := Fin n) (K := ℂ) E)+1)^m : ℕ) : ℝ)/T +
      (⌊((w*b+1)*(m+1:ℕ))/ζ⌋₊ : ℝ)/(((P i).card : ℝ)-(ell i+T)) ≤ η := by
    simpa only [totalSpace_finrank] using hη
  simpa only [Fintype.card_coe] using
    regular_adaptive_blocks P ell T m (fun z => physicalKernel (E := E) G d z.val)
      (fun z => physicalNext G d A h e z.val) start
      (fun z t => eval z.val t.2.minor) hmono X ζ (w*b+1) η ξ hX hζ hξ hp hsmall hminor
      hT hsize hη'

end QuarticPowerFree

end OAI
