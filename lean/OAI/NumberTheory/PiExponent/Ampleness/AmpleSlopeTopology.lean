import OAI.NumberTheory.PiExponent.Ampleness.AmpleSlopeAlgebra

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory Set
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def ampleSlopes (L H : LineBundle X) : Set ℝ :=
  {t | ∃ a b : ℕ, 0 < b ∧ t = (a : ℝ)/b ∧ (slopeBundle L H a b).IsAmple}

def ampleThreshold (L H : LineBundle X) : ℝ := sInf (ampleSlopes L H)

lemma ampleSlopes_bddBelow (L H : LineBundle X) : BddBelow (ampleSlopes L H) := by
  refine ⟨0, ?_⟩
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma ampleSlopes_nonempty [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : (ampleSlopes L H).Nonempty := by
  obtain ⟨a,ha,hA⟩ := exists_ample_slope L H hH
  exact ⟨(a:ℝ)/1,a,1,by decide,by norm_num,hA⟩

lemma ampleThreshold_nonneg [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : 0 ≤ ampleThreshold L H := by
  apply le_csInf (ampleSlopes_nonempty L H hH)
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ample_of_threshold_lt [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) (a b : ℕ) (hb : 0 < b)
    (ht : ampleThreshold L H < (a:ℝ)/b) : (slopeBundle L H a b).IsAmple := by
  obtain ⟨t,htmem,htt⟩ := exists_lt_of_csInf_lt (ampleSlopes_nonempty L H hH) ht
  obtain ⟨c,e,he,rfl,hA⟩ := htmem
  apply ample_slope_of_cross_le L H hH c e a b he hb _ hA
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast he : (0:ℝ)<e)
    (by exact_mod_cast hb : (0:ℝ)<b)).mp htt
  exact_mod_cast hcross.le

theorem threshold_lt_of_ample [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) : ampleThreshold L H < (a:ℝ)/b := by
  obtain ⟨n,hn,hsmall,hlt⟩ := exists_smaller_ample_slope L H a b ha hb hA
  have hmem : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) ∈ ampleSlopes L H :=
    ⟨a*n-1,b*n,Nat.mul_pos hb hn,rfl,hsmall⟩
  have hlt' : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) < (a:ℝ)/b := by
    have h := (Rat.cast_strictMono (K := ℝ)) hlt
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  exact (csInf_le (ampleSlopes_bddBelow L H) hmem).trans_lt hlt'

lemma slope_zero_isAmple_iff (L H : LineBundle X) (b : ℕ) (hb : 0 < b) :
    (slopeBundle L H 0 b).IsAmple ↔ L.IsAmple := by
  constructor
  · intro h
    apply LineBundle.IsAmple.of_pow L hb
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf) h
  · intro h
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf).symm (h.pow b hb)

lemma ampleThreshold_eq_zero_of_ample [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) (hL : L.IsAmple) : ampleThreshold L H = 0 := by
  apply le_antisymm _ (ampleThreshold_nonneg L H hH)
  apply csInf_le (ampleSlopes_bddBelow L H)
  exact ⟨0,1,by decide,by norm_num,(slope_zero_isAmple_iff L H 1 (by decide)).mpr hL⟩

end
end PiExponent.NumericalAmpleness

end OAI
