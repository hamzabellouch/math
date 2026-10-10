import OAI.Combinatorics.FiniteCircle.Parameters

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem coded_range_lower {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    {n k M : ℕ} [NeZero M] (hn : 1000000≤n) (hk : n^4=4*k)
    (hJ : Nat.log 2 M+1≤n^13)
    (H : AddSubgroup (I → ZMod M)) [Fintype H] (θ : I → ZMod M)
    (hb : ∀ χ : AddChar (I → ZMod M) ℂ, χ.compAddMonoidHom H.subtype=0 → χ θ≠1 →
      (((n^4:ℕ):ℝ)/2)^(n^4) ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ))
    (W : (I → ZMod M) → List α) (L copies : ℕ) (hL : 0<L)
    (hcL : L=M*Fintype.card I*copies) (hLen : ∀ v, (W v).length=L)
    (hcheap : ∀ v (c : H), (n^4)^(2*n^4)*editDistance (W v) (W (v+c)) ≤ 2*n^4*L)
    (hsingle : ∀ v i (j : Fin (Nat.log 2 M+1)),
      editDistance (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M))) ≤ 2*copies*2^j.val)
    (hlong : ∀ v, (L:ℝ)/(n:ℝ)^(3*n^4) ≤ (deficit (W v) (W (v+θ)):ℝ))
    {w : ℕ} (c : α → Fin w → Bool) (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ optimalDistortion (fun x : Set.range (fun v => encode c (W v)) => x.val) := by
  classical
  have hn0 : 0<n := by omega
  have hR : (0:ℝ)<((n^4)^(2*n^4):ℕ) := by positivity
  apply range_distortion_lower H θ ((((n^4:ℕ):ℝ)/2)^(n^4)) (by positivity) hb
    (fun v => encode c (W v)) (n^4) ((n^4)^(2*n^4):ℕ) L copies w
    ((1/268435456)*w/(n:ℝ)^(3*n^4)) ((n:ℝ)^k) (by positivity) (by have := hc.1; positivity)
    (by exact_mod_cast hcL)
  · intro v z
    apply (le_div_iff₀ hR).mpr
    have he := hc.2.2.2 (W v) (W (v+z))
    have ht := Nat.mul_le_mul_left ((n^4)^(2*n^4)) he
    have hh := Nat.mul_le_mul_left w (hcheap v z)
    have hn : editDistance (encode c (W v)) (encode c (W (v+z)))*((n^4)^(2*n^4)) ≤ w*2*n^4*L := by
      nlinarith
    exact_mod_cast hn
  · intro v i j
    have he := (hc.2.2.2 (W v) (W (v+Pi.single i ((2^j.val:ℕ):ZMod M)))).trans
      (Nat.mul_le_mul_left w (hsingle v i j))
    have hn : editDistance (encode c (W v)) (encode c (W (v+Pi.single i ((2^j.val:ℕ):ZMod M)))) ≤
        w*2*copies*2^j.val := by nlinarith
    exact_mod_cast hn
  · intro v
    have hd := (hc.2.2.1 L (W v) (W (v+θ)) (hLen v) (hLen (v+θ))).1
    have he := deficit_le_editDistance (x:=encode c (W v)) (y:=encode c (W (v+θ))) (by simp only [length_encode,hLen])
    calc
      _ = (1/268435456)*w*((L:ℝ)/(n:ℝ)^(3*n^4)) := by ring
      _ ≤ (1/268435456)*w*(deficit (W v) (W (v+θ)):ℝ) :=
        mul_le_mul_of_nonneg_left (hlong v) (by positivity)
      _ ≤ (deficit (encode c (W v)) (encode c (W (v+θ))):ℝ) := hd
      _ ≤ _ := by exact_mod_cast he
  · intro t _ ht
    apply lower_numeric hn hk hJ hc.1 t
    simpa only [Nat.cast_pow] using ht

 theorem flatMaskState_surjective (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ) :
    Function.Surjective (flatMaskState h p M l) := by
  classical
  induction l with
  | zero => intro v; exact ⟨fun _ => v,rfl⟩
  | succ l ih =>
    intro v
    choose f hf using fun j => ih (v j)
    refine ⟨fun i => f i.1 i.2, ?_⟩
    funext j
    exact hf j

 theorem flatExcludedState_surjective (h M l : ℕ) :
    Function.Surjective (flatExcludedState h M l) := by
  classical
  induction l with
  | zero => intro v; exact ⟨fun _ => v,rfl⟩
  | succ l ih =>
    intro v
    choose f hf using fun j => ih (v j)
    refine ⟨fun i => f i.1 i.2, ?_⟩
    funext j
    exact hf j

 theorem range_comp_surjective {X Y Z : Type*} (f : X → Y) (g : Y → Z) (hf : Function.Surjective f) :
    Set.range (fun x => g (f x)) = Set.range g := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨f x,rfl⟩
  · rintro ⟨y,rfl⟩; obtain ⟨x,rfl⟩ := hf y; exact ⟨x,rfl⟩

 theorem mask_length_factor (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ) :
    maskLength h p R M l = M*Fintype.card (TreeLeaf (MaskChildren h p) l)*treeCopies R (period h p) l := by
  apply tree_length_eq (MaskChildren h p) M R (period h p) (maskLength h p R M) rfl
  intro l
  simp only [maskLength, length_maskTags]
  congr 2
  simp only [MaskChildren, Fintype.card_sigma, Fintype.card_fin]

 theorem excluded_length_factor (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ) :
    excludedLength h p R M l = M*Fintype.card (TreeLeaf (fun _ => Fin h) l)*treeCopies R (period h p) l := by
  apply tree_length_eq (fun _ => Fin h) M R (period h p) (excludedLength h p R M) rfl
  intro l
  simp only [excludedLength,length_excludedTags,Fintype.card_fin]

 theorem mask_binary_distortion {n k : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {w : ℕ}
    (c : MaskAlphabet (n^4) p (n^4) → Fin w → Bool)
    (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ setDistortion (Set.range fun v : MaskState (n^4) p (circleSize (n^4) p) (n^4) =>
      encode c (maskWord (n^4) p ((n^4)^(2*n^4)) (circleSize (n^4) p) (n^4) v)) := by
  classical
  let h := n^4
  let M := circleSize h p
  let R := h^(2*h)
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 2≤h := (show 2≤n by omega).trans (le_self_pow₀ (by omega) (by norm_num))
  have hR : 0<R := pow_pos (by omega) _
  let H := maskCheap h p M hp.divides_circle h
  let : Fintype H := Fintype.ofFinite H
  have hhb (χ : AddChar (TreeLeaf (MaskChildren h p) h → ZMod M) ℂ)
      (ha : χ.compAddMonoidHom H.subtype=0) (hw : χ (fun _ => ((M/2:ℕ):ZMod M))≠1) :
      ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
    apply mask_character_branching hh hp.divides_circle hp.positive
      (fun l k hl hlh => (hp.atLevel l hl hlh k).1)
      hp.level_injective (fun l k hl hlh => (hp.atLevel l hl hlh k).2.1.le) χ ha _ hw
  have hlong (v : TreeLeaf (MaskChildren h p) h → ZMod M) :
      (maskLength h p R M h:ℝ)/(n:ℝ)^(3*n^4) ≤
        (deficit (flatMaskWord h p R M h v) (flatMaskWord h p R M h (v+(fun _ => ((M/2:ℕ):ZMod M)))):ℝ) := by
    have he : n^4=2*(n^4/2) := by omega
    have ht := mask_long_deficit hn he hp hR (flatMaskState h p M h v)
    have hf := flatMaskState_shift h p M h v ((M/2:ℕ):ZMod M)
    change flatMaskState h p M h (v+(fun _ => ((M/2:ℕ):ZMod M))) = _ at hf
    simpa only [flatMaskWord,hf] using ht
  have ht := coded_range_lower hn hk (hp.log_circle_fourth hn) H (fun _ => ((M/2:ℕ):ZMod M)) hhb
    (flatMaskWord h p R M h) (maskLength h p R M h) (treeCopies R (period h p) h)
    (hp.mask_length_pos (by omega) hR h) (mask_length_factor h p R M h)
    (fun v => length_maskWord h p R M h (flatMaskState h p M h v))
    (fun v z => mask_cheap_ed hR hp.divides_circle hp.positive hp.coprime h v z z.property)
    (fun v i j => mask_single_ed (StandingPrimes.circle_even (h:=h) (p:=p)) h v i (2^j.val)) hlong c hc
  have he := range_comp_surjective (flatMaskState h p M h)
    (fun v => encode c (maskWord h p R M h v)) (flatMaskState_surjective h p M h)
  unfold flatMaskWord at ht
  rw [he] at ht
  exact ht
 theorem excluded_binary_distortion {n k : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {w : ℕ}
    (c : ExcludedAlphabet (n^4) (circleSize (n^4) p) (n^4) → Fin w → Bool)
    (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ setDistortion (Set.range fun v : ExcludedState (n^4) (circleSize (n^4) p) (n^4) =>
      encode c (excludedWord (n^4) p ((n^4)^(2*n^4)) (circleSize (n^4) p) (n^4) v)) := by
  classical
  let h := n^4
  let M := circleSize h p
  let R := h^(2*h)
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 2≤h := (show 2≤n by omega).trans (le_self_pow₀ (by omega) (by norm_num))
  have hR : 0<R := pow_pos (by omega) _
  let H := excludedCheap h p M hp.divides_circle h
  let : Fintype H := Fintype.ofFinite H
  have hhb (χ : AddChar (TreeLeaf (fun _ => Fin h) h → ZMod M) ℂ)
      (ha : χ.compAddMonoidHom H.subtype=0) (hw : χ (fun _ => ((M/2:ℕ):ZMod M))≠1) :
      ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
    apply excluded_character_branching hh hp.divides_circle hp.positive
      (fun l k hl hlh => (hp.atLevel l hl hlh k).1)
      hp.level_injective (fun l k hl hlh => (hp.atLevel l hl hlh k).2.1.le) χ ha _ hw
  have hlong (v : TreeLeaf (fun _ => Fin h) h → ZMod M) :
      (excludedLength h p R M h:ℝ)/(n:ℝ)^(3*n^4) ≤
        (deficit (flatExcludedWord h p R M h v) (flatExcludedWord h p R M h (v+(fun _ => ((M/2:ℕ):ZMod M)))):ℝ) := by
    have he : n^4=2*(n^4/2) := by omega
    have ht := excluded_long_deficit hn he hp hR (flatExcludedState h M h v)
    have hf := flatExcludedState_shift h M h v ((M/2:ℕ):ZMod M)
    change flatExcludedState h M h (v+(fun _ => ((M/2:ℕ):ZMod M))) = _ at hf
    simpa only [flatExcludedWord,hf] using ht
  have ht := coded_range_lower hn hk (hp.log_circle_fourth hn) H (fun _ => ((M/2:ℕ):ZMod M)) hhb
    (flatExcludedWord h p R M h) (excludedLength h p R M h) (treeCopies R (period h p) h)
    (hp.excluded_length_pos (by omega) hR h) (excluded_length_factor h p R M h)
    (fun v => length_excludedWord h p R M h (flatExcludedState h M h v))
    (fun v z => excluded_cheap_ed hR hp.divides_circle hp.positive hp.coprime h v z z.property)
    (fun v i j => excluded_single_ed (StandingPrimes.circle_even (h:=h) (p:=p)) h v i (2^j.val)) hlong c hc
  have he := range_comp_surjective (flatExcludedState h M h)
    (fun v => encode c (excludedWord h p R M h v)) (flatExcludedState_surjective h M h)
  unfold flatExcludedWord at ht
  rw [he] at ht
  exact ht

end FiniteCircle

end OAI
