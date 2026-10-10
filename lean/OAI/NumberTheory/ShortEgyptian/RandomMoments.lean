import OAI.NumberTheory.ShortEgyptian.RandomBounds

namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_product_second_moment {J : Type uJ} {A : Type uA} [Fintype J] [Fintype A] [Nonempty A]
    (S : ℝ) (hcard : Fintype.card J = ⌊S/Real.log S⌋₊) (hlog : 1 ≤ Real.log S) (hS : 200*Real.log S ≤ S)
    (p : A → ℕ) (hp : ∀ a, (p a).Prime) (hinj : Function.Injective p)
    (hmax : ∀ a, (p a:ℝ) ≤ 2*S^100) (hP : S^99 ≤ (Fintype.card A:ℝ))
    (u l : ℕ) [NeZero u] (hu : 0 < u) (hl : 0 < l)
    (hV : 100000*Real.log S ≤ Real.log u) (hVS : Real.log u ≤ S)
    (hlmax : (l:ℝ) ≤ Real.exp ((1/200:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u))) :
    (𝔼 f : (J × Bool) → A,
      ‖𝔼 I : J → Bool,
        ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)‖^2) ≤
        Real.exp (-(1/100:ℝ)*min (⌊S/Real.log S⌋₊:ℝ) (Real.log u)) := by
  classical
  let m := ⌊S/Real.log S⌋₊
  let s := ⌊3*Real.log u/(400*Real.log S)⌋₊
  let V := Real.log u
  have hlen := random_lengths S V hlog hS hV hVS
  change S/(2*Real.log S) ≤ (m:ℝ) ∧ (m:ℝ) ≤ S ∧ V/(140*Real.log S) ≤ (s:ℝ) ∧
    (s:ℝ) ≤ 3*V/(400*Real.log S) ∧ 8*s ≤ m ∧ (s:ℝ) ≤ S ∧ 100 ≤ min (m:ℝ) V at hlen
  obtain ⟨hmL,hmS,hsL,hsU,h8,hsS,hw⟩ := hlen
  have hS2 : 2 ≤ S := by linarith
  have hSpos : 0 < S := by linarith
  have hVpos : 0 < V := by dsimp [V]; linarith
  have huR : 0 < (u:ℝ) := by exact_mod_cast hu
  have hscale : (l:ℝ)*Real.exp (V/10)*Real.exp (4/5*V) ≤ u :=
    random_reduced_scale u l hu hVpos.le
      (hlmax.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))))
  have hatom : (s:ℝ)^s/(Fintype.card A:ℝ)^s ≤ Real.exp (-(7/10:ℝ)*V) :=
    random_atom_bound S V _ s hS2 hP hsS hsL
  have hcorr (I K : J → Bool) (hIK : 2*s ≤ hammingDistance I K) :
      ‖𝔼 f : (J × Bool) → A,
        ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u)*
          (starRingEnd ℂ) (ZMod.stdAddChar ((l*sampleProduct p K f:ℕ):ZMod u))‖ ≤
        Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V) := by
    obtain ⟨L,R,hLD,hRD,hdis,hLs,hRs⟩ := disjoint_subsets_card
      (univ.filter (fun j => I j ≠ K j)) s hIK
    have hLs' : Fintype.card L = s := by simpa using hLs
    have hRs' : Fintype.card R = s := by simpa using hRs
    have hM : (𝔼 z : ((L∪R)ᶜ : Finset J) → A,
        (Nat.gcd (∏ j,p (z j)) u:ℝ)^(3/4:ℝ)) ≤ Real.exp 1 := by
      have hcount : (Fintype.card ((L∪R)ᶜ : Finset J):ℝ) ≤ S := by
        apply le_trans (b := (m:ℝ)) _ hmS
        simp only [Fintype.card_coe]
        exact_mod_cast (card_le_univ ((L∪R)ᶜ)).trans_eq hcard
      convert random_outside_moment S hS2 hcount p hp hinj hmax hP u hu hVS using 1
      apply expect_congr (by ext; simp)
      intro z _
      rfl
    have hh := pair_correlation_bound p hp hinj u l hu hl I K L R hdis (hRs.trans hLs.symm)
      (fun j hj => (mem_filter.mp (hLD hj)).2) (fun j hj => (mem_filter.mp (hRD hj)).2)
      (Real.exp (4/5*V)) (Real.exp (V/10)) (Real.exp (-(7/10:ℝ)*V)) (Real.exp 1) (3/4)
      (Real.exp_pos _) (Real.exp_nonneg _) (by norm_num) hscale (fun f => random_fresh_bound p S V hS2 hVpos hmax (by simpa only [hLs'] using hsU) f)
      (fun f => random_fresh_bound p S V hS2 hVpos hmax (by simpa only [hRs'] using hsU) f)
      (by simpa only [hLs] using hatom) hM
    exact hh.trans (random_pair_scalar u (by dsimp [V] at hVpos; linarith))
  have hh := mean_square_correlation_exp
    (fun I : J → Bool => fun f : (J × Bool) → A =>
      ZMod.stdAddChar ((l*sampleProduct p I f:ℕ):ZMod u))
    (fun I f => by simp) (2*s) (by simpa only [hcard, ←Nat.mul_assoc] using h8)
    (Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V)) (by positivity) hcorr
  apply hh.trans
  simpa only [hcard,add_assoc] using random_error_sum (m:ℝ) V hw

end ShortEgyptian

end OAI
