import OAI.Combinatorics.FiniteCircle.Upper

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem upperRates_sup_nonneg {α X : Type*} (word : X → List α) (f : X → RealL1) :
    0 ≤ sSup (upperRates word f) := by
  apply Real.sSup_nonneg
  rintro r ⟨x,y,_,rfl⟩
  positivity

 theorem lowerRates_sup_nonneg {α X : Type*} (word : X → List α) (f : X → RealL1) :
    0 ≤ sSup (lowerRates word f) := by
  apply Real.sSup_nonneg
  rintro r ⟨x,y,_,rfl⟩
  positivity

 theorem distortion_isometry_restrict {α β X Y : Type*} [Finite Y]
    (wordX : X → List α) (wordY : Y → List β) (g : X → Y) (hg : Function.Injective g)
    (he : ∀ x y, editDistance (wordY (g x)) (wordY (g y)) = editDistance (wordX x) (wordX y))
    (f : Y → RealL1) : distortion wordX (f ∘ g) ≤ distortion wordY f := by
  have hu : sSup (upperRates wordX (f ∘ g)) ≤ sSup (upperRates wordY f) := by
    apply Real.sSup_le _ (upperRates_sup_nonneg wordY f)
    rintro r ⟨x,y,hxy,rfl⟩
    apply le_csSup (upperRates_finite wordY f).bddAbove
    exact ⟨g x,g y,fun h => hxy (hg h),by simp only [Function.comp_apply,he]⟩
  have hl : sSup (lowerRates wordX (f ∘ g)) ≤ sSup (lowerRates wordY f) := by
    apply Real.sSup_le _ (lowerRates_sup_nonneg wordY f)
    rintro r ⟨x,y,hxy,rfl⟩
    apply le_csSup (lowerRates_finite wordY f).bddAbove
    exact ⟨g x,g y,fun h => hxy (hg h),by simp only [Function.comp_apply,he]⟩
  exact mul_le_mul hu hl (lowerRates_sup_nonneg wordX (f ∘ g)) (upperRates_sup_nonneg wordY f)

 theorem optimalDistortion_isometry_mono {α β X Y : Type*} [Fintype Y]
    (wordX : X → List α) (wordY : Y → List β) (g : X → Y) (hg : Function.Injective g)
    (he : ∀ x y, editDistance (wordY (g x)) (wordY (g y)) = editDistance (wordX x) (wordX y)) :
    optimalDistortion wordX ≤ optimalDistortion wordY := by
  apply optimalDistortion_lower
  intro f hf
  exact (optimalDistortion_le wordX (f ∘ g) (hf.comp hg)).trans
    (distortion_isometry_restrict wordX wordY g hg he f)

instance wordsFinite (α : Type*) [Finite α] (d : ℕ) : Finite (Words α d) :=
  (List.finite_length_le α d).to_subtype

 theorem words_nontrivial (α : Type*) [Nonempty α] {d : ℕ} (hd : 1≤d) : Nontrivial (Words α d) := by
  classical
  let a : α := Classical.ofNonempty
  refine ⟨⟨⟨[],by simp⟩,⟨[a],by simpa using hd⟩,?_⟩⟩
  intro he
  have ht := congrArg (fun x : Words α d => x.val.length) he
  simp at ht

 theorem binary_alphabet_embedding (α : Type*) [Fintype α] (hα : 2≤Fintype.card α) :
    ∃ (f : Bool → α) (g : α → Bool), Function.LeftInverse g f := by
  classical
  let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hα
  obtain ⟨a,b,hab⟩ := exists_pair_ne α
  refine ⟨fun t => cond t b a,fun x => decide (x=b),?_⟩
  intro t
  cases t <;> simp [hab]

 theorem setDistortion_le_E (α : Type*) [Fintype α] (hα : 2≤Fintype.card α)
    {S : Set (List Bool)} {d : ℕ} (hS : ∀ x∈S, x.length≤d) : setDistortion S≤E α d := by
  classical
  let : Fintype (Words α d) := Fintype.ofFinite _
  obtain ⟨f,g,hgf⟩ := binary_alphabet_embedding α hα
  let e : S → Words α d := fun x => ⟨x.val.map f,by simpa using hS x.val x.property⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (hgf.injective.list_map (congrArg Subtype.val hxy))
  apply optimalDistortion_isometry_mono (fun x : S => x.val) (fun x : Words α d => x.val) e he
  intro x y
  exact editDistance_map_eq f g hgf x.val y.val

 theorem maskWitness_lower_E {a C δ c : ℝ} {d : ℕ} (hw : MaskWitness a C δ c d)
    (α : Type*) [Fintype α] (hα : 2≤Fintype.card α) : Real.exp (c*exponentScale d)≤E α d := by
  rcases hw with ⟨h,_,p,_,w,code,_,_,n,_,hnd,hlen,hD⟩
  apply hD.trans (setDistortion_le_E α hα _)
  rintro x ⟨v,rfl⟩
  exact (hlen v).le.trans hnd

 theorem uniformUpper_E {C : ℝ} {d₀ : ℕ} (hu : UniformUpper C d₀)
    (α : Type) [Fintype α] (hα : 2≤Fintype.card α) {d : ℕ} (hd : d₀≤d) (hd1 : 1≤d) :
    E α d≤Real.exp (C*exponentScale d) := by
  classical
  let : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.mp hα
  let : Nontrivial (Words α d) := words_nontrivial α hd1
  obtain ⟨M,F,hF⟩ := hu α hα d hd
  let f : Words α d → RealL1 := fun x => finiteL1 M (F x)
  have hb := distortion_upper (fun x : Words α d => x.val) Subtype.val_injective
    f (Real.exp (C*exponentScale d)) 1 (Real.exp_pos _).le
    (fun x y => by simpa only [f,finiteL1_norm_sub] using (hF x y).2)
    (fun x y => by simpa only [f,one_mul,finiteL1_norm_sub] using (hF x y).1)
  exact (optimalDistortion_le (fun x : Words α d => x.val) f hb.1).trans (by simpa only [mul_one] using hb.2)

 theorem alphabetSupremum_bounds {d : ℕ} {lo hi : ℝ}
    (hb : ∀ A : ℕ, 2≤A → lo≤E (Fin A) d ∧ E (Fin A) d≤hi) :
    lo≤alphabetSupremum d ∧ alphabetSupremum d≤hi := by
  have hne : {r : ℝ | ∃ A : ℕ, 2≤A ∧ r=E (Fin A) d}.Nonempty := ⟨_,2,by norm_num,rfl⟩
  have hub : BddAbove {r : ℝ | ∃ A : ℕ, 2≤A ∧ r=E (Fin A) d} := by
    refine ⟨hi,?_⟩
    rintro r ⟨A,hA,rfl⟩
    exact (hb A hA).2
  refine ⟨(hb 2 (by norm_num)).1.trans (le_csSup hub ⟨2,by norm_num,rfl⟩),?_⟩
  apply csSup_le hne
  rintro r ⟨A,hA,rfl⟩
  exact (hb A hA).2

theorem full_main : FullMain := by
  obtain ⟨u,hu⟩ := uniform_upper
  let d₀ := max u (lowerCap 1000000)
  have hlow {d : ℕ} (hd : d₀≤d) : lowerCap 1000000≤d := (le_max_right _ _).trans hd
  have hu' : UniformUpper 32 d₀ := by
    intro α _ hα d hd
    exact hu α hα d ((le_max_left _ _).trans hd)
  have hb : ∀ (α : Type) [Fintype α], 2≤Fintype.card α → ∀ d : ℕ, d₀≤d →
      Real.exp ((1/8192)*exponentScale d)≤E α d ∧ E α d≤Real.exp (32*exponentScale d) := by
    intro α _ hα d hd
    have hd1 : 1≤d := by have := lowerCap_ge 1000000; have := hlow hd; omega
    exact ⟨maskWitness_lower_E (both_witnesses (hlow hd)).1 α hα,
      uniformUpper_E hu' α hα hd hd1⟩
  refine ⟨1/8192,32,1/268435456,67108928,1/1048576,1/1048576,d₀,
    by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,
    two_codes,hu',hb,?_⟩
  intro d hd
  have hw := both_witnesses (hlow hd)
  refine ⟨hw.1,hw.2,?_⟩
  exact alphabetSupremum_bounds (fun A hA => hb (Fin A) (by simpa using hA) d hd)

end FiniteCircle

theorem finiteCircle_fullMain : FiniteCircle.FullMain := FiniteCircle.full_main

end OAI
