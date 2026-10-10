import OAI.NumberTheory.GaussianMoat.DifferenceSampling

namespace OAI

universe uOmega uAlpha uBeta uGamma uIota uDelta uEpsilon uZeta

namespace GaussianMoat

namespace FinLaw

section

variable {Ω : Type uOmega} [Fintype Ω]

noncomputable def Hf {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) : ℝ := by
  classical
  exact -∑ ω, p ω * Real.log (∑ ν, if X ν = X ω then p ν else 0)

noncomputable def cHf {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  p.Hf (fun ω => (X ω,Y ω))-p.Hf Y

theorem Hf_eq_H {α : Type uAlpha} [Fintype α] (p : FinLaw Ω) (X : Ω → α) : p.Hf X = p.H X := by
  classical
  rw [H_eq_sum]
  simp only [Hf,map_mass]

theorem Hf_eq_of_fibers {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (hf : ∀ ω ν, X ω = X ν ↔ Y ω = Y ν) : p.Hf X = p.Hf Y := by
  classical
  unfold Hf
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  congr 2
  apply Finset.sum_congr rfl
  intro ν _
  rw [hf]

noncomputable def outputRange {α : Type uAlpha} (X : Ω → α) : Finset α := by
  classical
  exact Finset.univ.image X

noncomputable def outputCode {α : Type uAlpha} (X : Ω → α) (ω : Ω) : outputRange X :=
  ⟨X ω,by
    classical
    simp [outputRange]⟩

@[simp] theorem outputCode_eq_iff {α : Type uAlpha} (X : Ω → α) (ω ν : Ω) :
    outputCode X ω = outputCode X ν ↔ X ω = X ν := Subtype.ext_iff

theorem Hf_code {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) :
    p.Hf X = p.H (outputCode X) := by
  rw [← Hf_eq_H]
  exact p.Hf_eq_of_fibers _ _ (fun _ _ => (outputCode_eq_iff _ _ _).symm)

theorem Hf_pair_code {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) = p.H (fun ω => (outputCode X ω,outputCode Y ω)) := by
  rw [← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,outputCode_eq_iff,implies_true]

theorem Hf_triple_code {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω))) =
      p.H (fun ω => (outputCode X ω,(outputCode Y ω,outputCode Z ω))) := by
  rw [← Hf_eq_H]
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,outputCode_eq_iff,implies_true]

theorem Hf_nonneg {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) : 0 ≤ p.Hf X := by
  rw [Hf_code]
  exact (p.map _).entropy_nonneg

theorem Hf_le_log_card_sample {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → α) :
    p.Hf X ≤ Real.log (Fintype.card Ω) := by
  rw [Hf_code]
  refine (p.map _).entropy_le_log_card.trans ?_
  have hsel := Fintype.card_le_of_surjective (outputCode X) (fun ⟨x,hx⟩ => by
    classical
    obtain ⟨ω,_,hω⟩ := Finset.mem_image.mp hx
    exact ⟨ω,Subtype.ext hω⟩)
  exact Real.log_le_log (by exact_mod_cast Fintype.card_pos_iff.mpr (p.map (outputCode X)).nonempty)
    (by exact_mod_cast hsel)

theorem Hf_pair_comm {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) = p.Hf (fun ω => (Y ω,X ω)) := by
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,and_comm,implies_true]

theorem Hf_pair_assoc {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω))) = p.Hf (fun ω => ((X ω,Y ω),Z ω)) := by
  apply p.Hf_eq_of_fibers
  simp only [Prod.mk.injEq,and_assoc,implies_true]

theorem Hf_pair_ge_snd {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf Y ≤ p.Hf (fun ω => (X ω,Y ω)) := by
  rw [Hf_pair_code,Hf_code]
  exact p.H_pair_ge_snd _ _

theorem Hf_pair_subadd {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.Hf (fun ω => (X ω,Y ω)) ≤ p.Hf X+p.Hf Y := by
  rw [Hf_pair_code,Hf_code p X,Hf_code p Y]
  exact p.H_pair_subadd _ _

theorem Hf_strong_subadd {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.Hf (fun ω => (X ω,(Y ω,Z ω)))+p.Hf Y ≤
      p.Hf (fun ω => (X ω,Y ω))+p.Hf (fun ω => (Y ω,Z ω)) := by
  rw [Hf_triple_code,Hf_code p Y,Hf_pair_code p X Y,Hf_pair_code p Y Z]
  exact p.H_strong_subadd _ _ _

theorem cHf_nonneg {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ p.cHf X Y := sub_nonneg.mpr (p.Hf_pair_ge_snd X Y)

theorem cHf_le_Hf {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) :
    p.cHf X Y ≤ p.Hf X := by have := p.Hf_pair_subadd X Y; unfold cHf; linarith

theorem cHf_mono {α : Type uAlpha} {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf X (fun ω => (Y ω,Z ω)) ≤ p.cHf X Y := by
  have := p.Hf_strong_subadd X Y Z
  unfold cHf
  linarith

theorem Hf_comp_le {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (f : α → β) :
    p.Hf (f ∘ X) ≤ p.Hf X := by
  have h := p.Hf_pair_ge_snd X (f ∘ X)
  have he : p.Hf (fun ω => (X ω,(f ∘ X) ω)) = p.Hf X :=
    p.Hf_eq_of_fibers _ _ (fun _ _ => by
      simp only [Prod.mk.injEq,Function.comp_def]
      exact ⟨And.left,fun hh => ⟨hh,congrArg f hh⟩⟩)
  rwa [he] at h

theorem Hf_le_of_determined {α : Type uAlpha} {β : Type uBeta} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β)
    (h : ∀ ω ν, Y ω = Y ν → X ω = X ν) : p.Hf X ≤ p.Hf Y := by
  have hh := p.Hf_pair_ge_snd Y X
  have he : p.Hf (fun ω => (Y ω,X ω)) = p.Hf Y :=
    p.Hf_eq_of_fibers _ _ (fun ω ν => by
      simp only [Prod.mk.injEq]
      exact ⟨And.left,fun hh => ⟨hh,h ω ν hh⟩⟩)
  rwa [he] at hh

theorem Hf_const {α : Type uAlpha} (p : FinLaw Ω) (a : α) : p.Hf (fun _ => a) = 0 := by
  classical
  simp [Hf,p.sum_one]

theorem Hf_finset_subadd {ι : Type uIota} {α : Type uAlpha} (p : FinLaw Ω) (X : Ω → ι → α) (S : Finset ι) :
    p.Hf (fun ω (i : S) => X ω i) ≤ ∑ i ∈ S, p.Hf (fun ω => X ω i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : p.Hf (fun ω (i : (∅:Finset ι)) => X ω i) = p.Hf (fun _ => ()) := by
      apply p.Hf_eq_of_fibers
      intro ω ν
      simp only [iff_true]
      funext i
      exact False.elim (Finset.notMem_empty i.val i.property)
    simp [he,p.Hf_const]
  | @insert i S hi ih =>
    have he : p.Hf (fun ω (j : (insert i S : Finset ι)) => X ω j) =
        p.Hf (fun ω => (X ω i,fun j : S => X ω j)) := by
      apply p.Hf_eq_of_fibers
      intro ω ν
      constructor
      · intro h
        apply Prod.ext
        · exact congrFun h ⟨i,Finset.mem_insert_self _ _⟩
        · funext j; exact congrFun h ⟨j,Finset.mem_insert_of_mem j.property⟩
      · intro h
        funext j
        rcases Finset.mem_insert.mp j.property with hj | hj
        · simpa [hj] using congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) ⟨j,hj⟩
    rw [he,Finset.sum_insert hi]
    have hh := p.Hf_pair_subadd (fun ω => X ω i) (fun ω (j : S) => X ω j)
    linarith

end
open scoped BigOperators

variable {Ω : Type uOmega} {α : Type uAlpha} [Fintype Ω] {k : ℕ}

def prefixVar (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (s : ℕ) (ω : Ω) (i : Fin k) : Option α :=
  if i.val < s then some (X ω (π i)) else none

noncomputable def orderedEntropy (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ) : ℝ :=
  𝔼 π : Equiv.Perm (Fin k), p.Hf (prefixVar X π s)

omit [Fintype Ω] in
@[simp] theorem prefixVar_zero (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (ω : Ω) :
    prefixVar X π 0 ω = fun _ => none := by funext i; simp [prefixVar]

@[simp] theorem orderedEntropy_zero (p : FinLaw Ω) (X : Ω → Fin k → α) :
    p.orderedEntropy X 0 = 0 := by
  have h (π : Equiv.Perm (Fin k)) : prefixVar X π 0 = fun _ _ => none := by
    funext ω i
    simp [prefixVar]
  simp [orderedEntropy,h,Finset.expect,p.Hf_const]

theorem orderedEntropy_nonneg (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ) :
    0 ≤ p.orderedEntropy X s := Finset.expect_nonneg (fun _ _ => p.Hf_nonneg _)

theorem prefixVar_chain (p : FinLaw Ω) (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k))
    {s : ℕ} (hs : s < k) :
    p.Hf (prefixVar X π (s+1)) =
      p.Hf (fun ω => (X ω (π ⟨s,hs⟩),prefixVar X π s ω)) := by
  apply p.Hf_eq_of_fibers
  intro ω ν
  constructor
  · intro h
    apply Prod.ext
    · have hh := congrFun h ⟨s,hs⟩
      simpa [prefixVar] using hh
    · funext i
      by_cases hi : i.val < s
      · have hh := congrFun h i
        simpa [prefixVar,hi,show i.val<s+1 by omega] using hh
      · simp [prefixVar,hi]
  · intro h
    funext i
    by_cases hi : i.val < s
    · have hh := congrFun (congrArg Prod.snd h) i
      simpa [prefixVar,hi,show i.val<s+1 by omega] using hh
    · by_cases his : i.val = s
      · have hieq : i = ⟨s,hs⟩ := Fin.ext his
        subst i
        simpa [prefixVar] using congrArg some (congrArg Prod.fst h)
      · simp [prefixVar,show ¬i.val<s+1 by omega]

theorem orderedEntropy_step (p : FinLaw Ω) (X : Ω → Fin k → α) {s : ℕ} (hs : s < k) :
    p.orderedEntropy X (s+1)-p.orderedEntropy X s =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π ⟨s,hs⟩)) (prefixVar X π s) := by
  simp only [orderedEntropy,← Finset.expect_sub_distrib,cHf,p.prefixVar_chain X _ hs]

theorem ordered_remaining_exchange (p : FinLaw Ω) (X : Ω → Fin k → α) (s : ℕ)
    (i j : Fin k) (hi : s ≤ i.val) (hj : s ≤ j.val) :
    (𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π i)) (prefixVar X π s)) =
      𝔼 π : Equiv.Perm (Fin k), p.cHf (fun ω => X ω (π j)) (prefixVar X π s) := by
  classical
  apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
  intro π
  have hp : prefixVar X (π*Equiv.swap i j) s = prefixVar X π s := by
    funext ω a
    by_cases ha : a.val<s
    · have hai : a≠i := by intro he; subst a; omega
      have haj : a≠j := by intro he; subst a; omega
      simp [prefixVar,ha,Equiv.Perm.mul_apply,Equiv.swap_apply_of_ne_of_ne hai haj]
    · simp [prefixVar,ha]
  change p.cHf (fun ω => X ω (π i)) (prefixVar X π s) =
    p.cHf (fun ω => X ω ((π * Equiv.swap i j) j)) (prefixVar X (π * Equiv.swap i j) s)
  rw [hp]
  simp only [Equiv.Perm.mul_apply,Equiv.swap_apply_right]

theorem cHf_mono_of_refines {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Z : Ω → γ)
    (h : ∀ ω ν, Y ω = Y ν → Z ω = Z ν) : p.cHf X Y ≤ p.cHf X Z := by
  have hc := p.cHf_mono X Z Y
  have hy : p.Hf (fun ω => (Z ω,Y ω)) = p.Hf Y := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨And.right,fun hh => ⟨h ω ν hh,hh⟩⟩
  have hx : p.Hf (fun ω => (X ω,(Z ω,Y ω))) = p.Hf (fun ω => (X ω,Y ω)) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun hh => ⟨hh.1,hh.2.2⟩,fun hh => ⟨hh.1,h ω ν hh.2,hh.2⟩⟩
  unfold cHf at hc ⊢
  rwa [hy,hx] at hc

theorem orderedEntropy_concave (p : FinLaw Ω) (X : Ω → Fin k → α) {s : ℕ} (hs : s+1 < k) :
    p.orderedEntropy X (s+2)-p.orderedEntropy X (s+1) ≤
      p.orderedEntropy X (s+1)-p.orderedEntropy X s := by
  rw [p.orderedEntropy_step X hs,p.orderedEntropy_step X (by omega : s<k)]
  rw [p.ordered_remaining_exchange X s ⟨s,by omega⟩ ⟨s+1,hs⟩ (by exact le_rfl) (by exact Nat.le_succ s)]
  apply Finset.expect_le_expect
  intro π _
  apply p.cHf_mono_of_refines
  intro ω ν hh
  funext a
  by_cases ha : a.val < s
  · simpa [prefixVar,ha,show a.val < s+1 by omega] using congrFun hh a
  · simp [prefixVar,ha]

theorem orderedEntropy_slope (p : FinLaw Ω) (X : Ω → Fin k → α)
    {b : ℕ} (hb : 0 < b) (hbk : b < k) :
    p.orderedEntropy X (b+1)-p.orderedEntropy X b ≤ p.orderedEntropy X b / b := by
  have h (s : ℕ) (hs : s < k) :
      (s : ℝ)*(p.orderedEntropy X (s+1)-p.orderedEntropy X s) ≤ p.orderedEntropy X s := by
    induction s with
    | zero => simp
    | succ s ih =>
      have ih' := ih (by omega)
      have hc := p.orderedEntropy_concave X hs
      have hn : (0 : ℝ) ≤ s+1 := by positivity
      have hm := mul_le_mul_of_nonneg_left hc hn
      simp only [Nat.cast_add,Nat.cast_one] at *
      nlinarith
  exact (le_div_iff₀ (by exact_mod_cast hb)).mpr (by nlinarith [h b hbk])

noncomputable def signedEntropy (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α) (s : ℕ) : ℝ :=
  𝔼 σ : Fin k → Bool, p.orderedEntropy (X σ) s

@[simp] theorem signedEntropy_zero (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α) :
    p.signedEntropy X 0 = 0 := by simp [signedEntropy,Finset.expect]

theorem signedEntropy_slope (p : FinLaw Ω) (X : (Fin k → Bool) → Ω → Fin k → α)
    {b : ℕ} (hb : 0 < b) (hbk : b < k) :
    p.signedEntropy X (b+1)-p.signedEntropy X b ≤ p.signedEntropy X b / b := by
  unfold signedEntropy
  rw [← Finset.expect_sub_distrib,Finset.expect_div]
  exact Finset.expect_le_expect (fun σ _ => p.orderedEntropy_slope (X σ) hb hbk)

theorem cHf_chain {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf (fun ω => (X ω,Y ω)) Z = p.cHf X Z + p.cHf Y (fun ω => (X ω,Z ω)) := by
  unfold cHf
  have he : p.Hf (fun ω => ((X ω,Y ω),Z ω)) = p.Hf (fun ω => (Y ω,(X ω,Z ω))) := by
    apply p.Hf_eq_of_fibers
    simp only [Prod.mk.injEq]
    tauto
  rw [he]
  ring

theorem cHf_pair_subadd {β : Type uBeta} {γ : Type uGamma} (p : FinLaw Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    p.cHf (fun ω => (X ω,Y ω)) Z ≤ p.cHf X Z + p.cHf Y Z := by
  rw [p.cHf_chain]
  apply add_le_add le_rfl
  apply p.cHf_mono_of_refines
  intro ω ν h
  exact congrArg Prod.snd h

theorem enrichment_chain {β : Type uBeta} {γ : Type uGamma} {δ : Type uDelta} {ε : Type uEpsilon} {ζ : Type uZeta} (p : FinLaw Ω)
    (X : Ω → α) (Y : Ω → β) (Bx : Ω → γ) (By : Ω → δ) (h : Ω → ε) (H : Ω → ζ)
    (hh : ∀ ω ν, X ω = X ν → Y ω = Y ν → h ω = h ν)
    (hY : ∀ ω ν, X ω = X ν → h ω = h ν → Y ω = Y ν)
    (hH : ∀ ω ν, H ω = H ν → h ω = h ν) :
    p.cHf h (fun ω => (Bx ω,By ω)) ≤ p.cHf X Bx + p.cHf Y By -
      p.cHf X (fun ω => ((Bx ω,By ω),H ω)) := by
  let B := fun ω => (Bx ω,By ω)
  have he : p.cHf (fun ω => (h ω,X ω)) B = p.cHf (fun ω => (X ω,Y ω)) B := by
    unfold cHf
    congr 1
    apply p.Hf_eq_of_fibers
    intro ω ν
    simp only [Prod.mk.injEq]
    exact ⟨fun ha => ⟨⟨ha.1.2,hY ω ν ha.1.2 ha.1.1⟩,ha.2⟩,
      fun ha => ⟨⟨hh ω ν ha.1.1 ha.1.2,ha.1.1⟩,ha.2⟩⟩
  have hx : p.cHf X B ≤ p.cHf X Bx :=
    p.cHf_mono_of_refines _ _ _ (fun _ _ he => congrArg Prod.fst he)
  have hy : p.cHf Y B ≤ p.cHf Y By :=
    p.cHf_mono_of_refines _ _ _ (fun _ _ he => congrArg Prod.snd he)
  have ht : p.cHf X (fun ω => (B ω,H ω)) ≤ p.cHf X (fun ω => (h ω,B ω)) := by
    apply p.cHf_mono_of_refines
    intro ω ν he
    apply Prod.ext
    · exact hH ω ν (congrArg Prod.snd he)
    · exact congrArg Prod.fst he
  have hc := p.cHf_chain h X B
  have hs := p.cHf_pair_subadd X Y B
  change p.cHf h B ≤ p.cHf X Bx + p.cHf Y By - p.cHf X (fun ω => (B ω,H ω))
  linarith

end FinLaw

end GaussianMoat

end OAI
