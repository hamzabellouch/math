import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialCoupling
import OAI.Combinatorics.KMedianRecovery.Recovery.Leaf

namespace OAI

namespace MetricKMedianRecovery.PhaseGeometricMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing
  PhaseMergeInvariant PhaseInitialBracket
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

noncomputable def initial_coupling {loc : D → X} {F : Finset X} {v eta lo hi l u U : ℝ}
    {n k a b : ℕ} (hl : lo ≤ l) (hu : u ≤ hi) (hlu : l ≤ u) (hl0 : 0 ≤ l)
    (hwidth : u-l ≤ (Fintype.card D:ℝ)*eta)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j)) (hs : Sandwich k a b)
    (ha : Attains loc F ∅ ∅ v u 0 n a) (hb : Attains loc F ∅ ∅ v l 0 n b) :
    Coupled loc F v eta lo hi 0 n k U where
  B := ∅
  P := []
  r := id
  lam := l
  lam' := u
  eps := 0
  a := a
  b := b
  disjoint := (Finset.disjoint_empty_right F)
  low := hl
  high := hu
  price := hlu
  eps_nonneg := le_rfl
  error := by simpa only [mul_zero,add_zero] using hwidth
  inj := Function.injective_id
  fixed := fun _ _ => rfl
  shrink := fun _ _ _ => le_rfl
  loss := fun _ _ _ => by simp only [id_eq,add_zero,le_refl]
  old_prefix := empty_prefix loc F ∅ v l eta hl0 hfar
  new_prefix := by
    simpa only [Finset.image_empty,List.map_nil] using
      empty_prefix loc F ∅ v u eta (hl0.trans hlu) hfar
  sandwich := hs
  new_tail := by simpa only [Finset.image_empty,List.map_nil,after] using ha
  old_tail := hb
  old_geometry := PhaseLeafGeometry.empty loc F U
  new_geometry := by simpa only [Finset.image_empty] using PhaseLeafGeometry.empty loc F U

theorem produce [Nonempty D] (loc : D → X) (F : Finset X) (v eta : ℝ)
    (lo M : ℚ) (k N total : ℕ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heta : 0 ≤ eta) (hprec : (1:ℝ)/2^N ≤ eta)
    (hlo : 0 < lo) (hM : 0 < M) (hN : 3 ≤ N) (hnN : Fintype.card D ≤ N)
    (hk : 2 ≤ k) (hlohi : lo ≤ 8*(Fintype.card D:ℚ)*M)
    (hF : F.Nonempty) (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ (M:ℝ)) :
    (∃ c, c ≤ k ∧ Attains loc F ∅ ∅ v (lo:ℝ) 0 total c) ∨
      Solved loc F v eta (lo:ℝ) (8*(Fintype.card D:ℝ)*(M:ℝ)) total k (20*N*(M:ℝ)) := by
  classical
  let count (s : ℚ) : ℕ := Classical.choose
    (attains_exists loc F ∅ ∅ v (s:ℝ) 0 total (Finset.empty_subset _))
  have hc (s : ℚ) : Attains loc F ∅ ∅ v (s:ℝ) 0 total (count s) :=
    Classical.choose_spec (attains_exists loc F ∅ ∅ v (s:ℝ) 0 total (Finset.empty_subset _))
  by_cases hlow : count lo ≤ k
  · exact Or.inl ⟨count lo,hlow,hc lo⟩
  · right
    have hhigh : count (8*(Fintype.card D:ℚ)*M) ≤ k := by
      apply (PhaseUpperBracket.attains_high loc F v (M:ℝ) hv hvsmall (by exact_mod_cast hM) hdiam (n := total) (c := count (8*(Fintype.card D:ℚ)*M)) ?_).trans
        (by omega : 1 ≤ k)
      simpa only [Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast] using hc (8*(Fintype.card D:ℚ)*M)
    obtain ⟨l,u,hl,hlu,hu,hw,hcl,hcu⟩ := PriceBisection.close_bracket count k N lo
      (8*(Fintype.card D:ℚ)*M) hlohi (by omega) hhigh
    have hloR : (0:ℝ) < (lo:ℝ) := by exact_mod_cast hlo
    have hlR : (lo:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
    have hluR : (l:ℝ) ≤ (u:ℝ) := by exact_mod_cast hlu
    have huR : (u:ℝ) ≤ 8*(Fintype.card D:ℝ)*(M:ℝ) := by exact_mod_cast hu
    have hlp : (0:ℝ) < (l:ℝ) := hloR.trans_le hlR
    have hup : (0:ℝ) < (u:ℝ) := hlp.trans_le hluR
    by_cases hel : count l = k
    · have hp := empty_prefix loc F ∅ v (l:ℝ) eta hlp.le hfar
      have hs := finish hp hv hvsmall hlp heta (Finset.disjoint_empty_right F) hlR
        (hluR.trans huR) (PhaseLeafGeometry.empty loc F (20*N*(M:ℝ))) (hel ▸ hc l)
      simpa only [Nat.zero_add] using hs
    by_cases heu : count u = k
    · have hp := empty_prefix loc F ∅ v (u:ℝ) eta hup.le hfar
      have hs := finish hp hv hvsmall hup heta (Finset.disjoint_empty_right F) (hlR.trans hluR)
        huR (PhaseLeafGeometry.empty loc F (20*N*(M:ℝ))) (heu ▸ hc u)
      simpa only [Nat.zero_add] using hs
    have hwidth : (u:ℝ)-(l:ℝ) ≤ (Fintype.card D:ℝ)*eta := by
      have hwr : (u:ℝ)-(l:ℝ) ≤ (1:ℝ)/2^N := by
        have hh : ((u-l:ℚ):ℝ) ≤ ((1/(2:ℚ)^N:ℚ):ℝ) := Rat.cast_le.mpr hw
        push_cast at hh
        exact hh
      have hn : (1:ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
      exact (hwr.trans hprec).trans (by nlinarith only [mul_le_mul_of_nonneg_right hn heta])
    let cou := initial_coupling (U := 20*N*(M:ℝ)) hlR huR hluR hlp.le hwidth hfar
      (Or.inl ⟨by omega,by omega⟩ : Sandwich k (count u) (count l)) (hc u) (hc l)
    have hhalf : (1:ℝ)/2^(N+1) ≤ eta := by
      apply le_trans _ hprec
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hupper : 8*(Fintype.card D:ℝ)*(M:ℝ) ≤ 8*N*(M:ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (by norm_num)) (by exact_mod_cast hM.le)
    have hs := solve v eta (lo:ℝ) (8*(Fintype.card D:ℝ)*(M:ℝ)) M k N
      hv hvsmall hloR heta hhalf hM hN hupper total X loc F 0 hF hdiam cou
    simpa only [Nat.zero_add] using hs

end MetricKMedianRecovery.PhaseGeometricMerge

end OAI
