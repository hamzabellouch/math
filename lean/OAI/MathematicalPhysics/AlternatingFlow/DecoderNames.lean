import OAI.MathematicalPhysics.AlternatingFlow.ProfileNames
import OAI.MathematicalPhysics.AlternatingFlow.DecoderBounds

namespace OAI

section DecoderNamesDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

lemma decoderBound : Primrec₂ Quantitative.decoderBound :=
  Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp
      (nat_pow.comp (Primrec.nat_mul.comp (Primrec.const 3)
        (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))) Primrec.snd)
      (transitionBound.comp Primrec.snd))

lemma rat_fract : Primrec (fun q : ℚ => Int.fract q) :=
  Arithmetic.rat_sub.comp Primrec.id (Arithmetic.rat_intCast.comp Arithmetic.rat_floor)

lemma frac_cast (q : ℚ) : ((Int.fract q : ℚ) : ℝ) = Int.fract (q : ℝ) := by
  simp only [Int.fract, Rat.cast_sub, Rat.cast_intCast, Rat.floor_cast]

lemma periodizer_named : Named (fun z : (ℚ × ℚ) × ℚ => Profiles.periodizer z.1.1 z.1.2 z.2) := by
  have hv : Computable (fun z : (ℚ × ℚ) × ℚ => Int.fract z.2) := rat_fract.to_comp.comp Computable.snd
  have hA : Computable (fun z : (ℚ × ℚ) × ℚ => (Int.fract z.2 - z.1.1)/(z.1.2-z.1.1)) :=
    Arithmetic.rat_div.to_comp.comp
      (Arithmetic.rat_sub.to_comp.comp hv (Computable.fst.comp Computable.fst))
      (Arithmetic.rat_sub.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.fst.comp Computable.fst))
  exact ((Named.rational hv).sub (transition_named.comp hA)).congr (by
    intro z
    simp only [Function.comp_def, Profiles.periodizer, Rat.cast_div, Rat.cast_sub]
    rw [frac_cast])

lemma decoder_named : Named (fun z : ℕ × ℚ => Profiles.decoder z.1 (z.2 : ℝ)) := by
  let m (b : ℕ) : ℚ := ((b : ℚ)-2)/((b : ℚ)-1)
  have hm : Computable m := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 2))
    (Arithmetic.rat_sub.to_comp.comp Arithmetic.rat_natCast.to_comp (Computable.const 1))
  have ha : Computable (fun z : ℕ × ℚ => (2*m z.1+1)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp
      (Arithmetic.rat_mul.to_comp.comp (Computable.const 2) (hm.comp Computable.fst))
      (Computable.const 1)) (Computable.const 3)
  have hc : Computable (fun z : ℕ × ℚ => (m z.1+2)/3) := Arithmetic.rat_div.to_comp.comp
    (Arithmetic.rat_add.to_comp.comp (hm.comp Computable.fst) (Computable.const 2)) (Computable.const 3)
  exact (periodizer_named.comp ((ha.pair hc).pair Computable.snd)).congr (by
    intro z; simp [Profiles.decoder, Encoding.tailMax, m])

lemma Named.decoder {A : Type*} [Primcodable A] (b : A → ℕ) (hb : Computable b)
    (hbase : ∀ x, 2 ≤ b x) {f : A → ℝ} (hf : Named f) :
    Named (fun x => Profiles.decoder (b x) (f x)) := by
  let L (x : A) : ℚ := Quantitative.decoderBound (b x) 1
  have hL : Computable L := Arithmetic.rat_natCast.to_comp.comp
    (decoderBound.to_comp.comp hb (Computable.const 1))
  have hg : Named (fun z : A × ℚ => Profiles.decoder (b z.1) (z.2 : ℝ)) :=
    Named.comp (g := fun z : A × ℚ => (b z.1, z.2)) decoder_named
      ((hb.comp Computable.fst).pair Computable.snd)
  have hlip (a : A) (x y : ℝ) : |Profiles.decoder (b a) x - Profiles.decoder (b a) y| ≤
      (L a : ℝ) * |x-y| := by
    simpa only [L, Rat.cast_natCast] using jet_one_lipschitz (Profiles.decoder_smooth _ (hbase a))
      (Quantitative.decoderBound (b a) 1) (Quantitative.decoder_jet_bound (b a) (hbase a) 1) x y
  exact Named.apply_lipschitz (fun x => Profiles.decoder (b x)) L hL
    (fun _ => Nat.cast_nonneg _) hlip hg hf

end AlternatingNS.Effective

end DecoderNamesDevelopment

end OAI
