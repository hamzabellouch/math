import Mathlib
import OAI.Combinatorics.StripMass.NorthMerging

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
lemma polynomialNorthGluing_box (n : ℕ) :
    LaurentBox (polynomialNorthGluing n) (fun _ => 4*n) := by
  rw [polynomialNorthGluing, sourceGlue_eq_sum]
  apply LaurentBox.sum
  intro p _
  apply LaurentBox.sum
  intro q _
  split_ifs
  · rw [one_mul]
    convert (polynomialNorthSource_box n p).reflect.mul (polynomialNorthSource_box n q) using 1
    ext i
    change 4*n = 2*n+2*n
    omega
  · simp only [zero_mul,mul_zero]
    exact LaurentBox.zero _

lemma polynomialNorthGluing_reflection (n : ℕ) :
    reflectLaurent n (polynomialNorthGluing n) = polynomialNorthGluing n := by
  unfold polynomialNorthGluing
  rw [sourceGlue_map (reflectLaurent n) n]
  have h : reflectLaurent n ∘ (fun p => reflectLaurent n (polynomialNorthSource n p)) =
      polynomialNorthSource n := by
    funext p
    exact reflectLaurent_involutive n _
  rw [h]
  exact sourceGlue_symmetric (K:=Laurent n) n _ _

lemma map_occupancySign {K L : Type*} [Ring K] [Ring L]
    (f : K →+* L) {n : ℕ} (p : Pairing n) (i : Fin n) :
    f (occupancySign p i) = occupancySign p i := by
  unfold occupancySign
  split_ifs <;> simp

lemma sourceGlue_signTwist {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) (i : Fin (n+1)) :
    sourceGlue n (fun p => occupancySign p.val i * v p)
        (fun p => occupancySign p.val i * w p) = sourceGlue n v w := by
  rw [sourceGlue_eq_sum, sourceGlue_eq_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  split_ifs with h
  · rw [one_mul, one_mul]
    have hs : (occupancySign p.val i : K) = occupancySign q.val i := by
      simp only [occupancySign, h.2.1 i]
    rw [hs]
    calc
      _ = (occupancySign q.val i * occupancySign q.val i) * (v p * w q) := by ring
      _ = _ := by rw [occupancySign_mul_self,one_mul]
  · simp

lemma polynomialNorthGluing_eval (n : ℕ) :
    evalLaurent (polynomialNorthGluing n) =
      sourceGlue n (fun p => reflectSpectral n (evalLaurent (polynomialNorthSource n p)))
        (fun p => evalLaurent (polynomialNorthSource n p)) := by
  unfold polynomialNorthGluing evalLaurent
  rw [sourceGlue_map]
  change sourceGlue n (fun p => evalLaurent (reflectLaurent n (polynomialNorthSource n p)))
      (fun p => evalLaurent (polynomialNorthSource n p)) = _
  congr 1
  funext p
  exact (reflectSpectral_evalLaurent (polynomialNorthSource n p)).symm

 
lemma polynomialNorthGluing_parity (n : ℕ) (i : Fin n) :
    signLaurent i (polynomialNorthGluing n) = polynomialNorthGluing n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (signLaurent i (polynomialNorthGluing n)) =
    evalLaurent (polynomialNorthGluing n)
  rw [←signSpectral_evalLaurent, polynomialNorthGluing_eval, sourceGlue_map]
  simp only [Function.comp_def, ←reflectSpectral_sign, polynomialNorthSource_parity,
    map_mul, map_occupancySign]
  exact sourceGlue_signTwist n _ _ _

lemma perm_reflect_ratio {n : ℕ} (i j : Fin n) :
    permSpectral (Equiv.swap i j) (reflectSpectral n (variableF j / variableF i)) =
      variableF j / variableF i := by
  simp only [map_div₀, reflectSpectral_variable, map_pow, permSpectral_const,
    permSpectral_variable, Equiv.swap_apply_left, Equiv.swap_apply_right]
  field_simp [variableF_ne_zero, constF_phase_ne_zero]

lemma polynomialNorthSource_reflected_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (reflectSpectral n (evalLaurent (polynomialNorthSource n p)))) =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => reflectSpectral n (evalLaurent (polynomialNorthSource n p))) := by
  let σ := Equiv.swap (⟨r,by omega⟩ : Fin n) (⟨r+1,by omega⟩ : Fin n)
  let R : Matrix (SourcePairing n) (SourcePairing n) (SpectralField n) := sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))
  have hR : (R.map (reflectSpectral n)).map (permSpectral σ) = R := by
    unfold R σ
    rw [sourceBlock_map, localR_map_hom, reflectSpectral_torusWeights,
      sourceBlock_map, localR_map_hom, permSpectral_torusWeights, perm_reflect_ratio]
  have h := congrArg (fun V : SourcePairing n → SpectralField n =>
      fun p => permSpectral σ (reflectSpectral n (V p)))
    (polynomialNorthSource_covariance r hr)
  funext p
  have hh := congrFun h p
  change permSpectral σ (reflectSpectral n (evalLaurent (polynomialNorthSource n p))) =
    permSpectral σ (reflectSpectral n (R.mulVec
      (fun q => permSpectral σ (evalLaurent (polynomialNorthSource n q))) p)) at hh
  rw [RingHom.map_mulVec, RingHom.map_mulVec, hR] at hh
  change _ = R.mulVec (fun q => permSpectral σ (reflectSpectral n
    (permSpectral σ (evalLaurent (polynomialNorthSource n q))))) p at hh
  have hv : (fun q => permSpectral σ (reflectSpectral n
    (permSpectral σ (evalLaurent (polynomialNorthSource n q))))) =
      (fun q => reflectSpectral n (evalLaurent (polynomialNorthSource n q))) := by
    funext q
    rw [reflectSpectral_perm]
    exact permSpectral_swap_involutive ⟨r,by omega⟩ ⟨r+1,by omega⟩ _
  rw [hv] at hh
  exact hh

 

lemma polynomialNorthGluing_exchange {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    permLaurent (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩) (polynomialNorthGluing n) =
      polynomialNorthGluing n := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (permLaurent (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
    (polynomialNorthGluing n)) = evalLaurent (polynomialNorthGluing n)
  rw [←permSpectral_evalLaurent, polynomialNorthGluing_eval, sourceGlue_map]
  change sourceGlue n
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (reflectSpectral n (evalLaurent (polynomialNorthSource n p))))
    (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
      (evalLaurent (polynomialNorthSource n p))) = _
  rw [polynomialNorthSource_reflected_covariance r hr, ←sourceGlue_adjoint,
    ←polynomialNorthSource_covariance r hr]

 
def northSeparatorMoment (n : ℕ) : SpectralField n :=
  sourceGlue n (fun p => reflectSpectral n (integratedNorthSource n p))
    (integratedNorthSource n)

lemma sourceGlue_scale {K : Type*} [CommRing K] (n : ℕ) (a b : K)
    (v w : SourcePairing n → K) :
    sourceGlue n (a • v) (b • w) = (a*b)*sourceGlue n v w := by
  simp only [sourceGlue,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

 

theorem polynomialNorthGluing_eval_moment (n : ℕ) :
    evalLaurent (polynomialNorthGluing n) =
      spectralNormalization n ^ 2 * northSeparatorMoment n := by
  rw [polynomialNorthGluing_eval]
  simp only [polynomialNorthSource_eval,map_mul,reflectSpectral_normalization]
  change sourceGlue n (spectralNormalization n • _)
    (spectralNormalization n • integratedNorthSource n) = _
  rw [sourceGlue_scale,pow_two]
  rfl

end


 

noncomputable section
open scoped Classical
open Finset Relation
namespace Pairing

lemma adj_interior {n : ℕ} {p : Pairing n} {a b i j : Fin n}
    (hab : p.Adj a b) (hai : a < i) (hib : i < b) (hij : p.Adj i j) :
    a < j ∧ j < b := by
  have hia : i ≠ a := ne_of_gt hai
  have hib' : i ≠ b := ne_of_lt hib
  have hja : j ≠ a := by
    intro he
    subst j
    have hh := adj_unique hab (adj_symm hij)
    omega
  have hjb : j ≠ b := by
    intro he
    subst j
    have hh := adj_unique (adj_symm hab) (adj_symm hij)
    omega
  exact (not_cross_iff_between (hai.trans hib) hia hib' hja hjb).mp
    (not_cross hij hab) |>.mp ⟨hai, hib⟩

lemma fully_matched_interval_even {n : ℕ} {p : Pairing n}
    (hp : ∀ i, p.Occupied i) {a b : Fin n} (hab : p.Adj a b) (_hlt : a < b) :
    Even (b.val - a.val - 1) := by
  let I := {i : Fin n // i ∈ Finset.Ioo a b}
  let G : SimpleGraph I := ⟨fun i j => p.Adj i.1 j.1,
    ⟨fun _ _ h => adj_symm h⟩, ⟨fun _ => p.adj_irrefl _⟩⟩
  have hG : (⊤ : G.Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro i
    obtain ⟨j, hj⟩ := hp i
    have hjmem := adj_interior hab (Finset.mem_Ioo.mp i.2).1 (Finset.mem_Ioo.mp i.2).2 hj
    refine ⟨⟨j, Finset.mem_Ioo.mpr hjmem⟩, ?_, ?_⟩
    · exact hj
    · intro k hk
      exact Subtype.ext (adj_unique hk hj)
  have he := hG.even_card
  simpa only [I, Fintype.card_coe, Fin.card_Ioo] using he

 

def shiftedVisitAdj {n : ℕ} (i j : Fin n) : Prop :=
  (i.val % 2 = 1 ∧ j.val = i.val + 1) ∨
    (j.val % 2 = 1 ∧ i.val = j.val + 1)

def visitWiring {n : ℕ} (p : Pairing n) (i j : Fin n) : Prop :=
  p.Adj i j ∨ shiftedVisitAdj i j

lemma adj_closed_interval {n : ℕ} {p : Pairing n} {a b i j : Fin n}
    (hab : p.Adj a b) (h : a ≤ i ∧ i ≤ b) (hij : p.Adj i j) :
    a ≤ j ∧ j ≤ b := by
  by_cases ha : i = a
  · subst i
    have := adj_unique hij hab
    subst j
    exact ⟨h.1.trans h.2, le_rfl⟩
  by_cases hb : i = b
  · subst i
    have := adj_unique hij (adj_symm hab)
    subst j
    exact ⟨le_rfl, h.1.trans h.2⟩
  obtain ⟨haj, hjb⟩ := adj_interior hab (lt_of_le_of_ne h.1 (Ne.symm ha))
    (lt_of_le_of_ne h.2 hb) hij
  exact ⟨haj.le, hjb.le⟩

lemma shiftedVisitAdj_closed_interval {n : ℕ} {a b i j : Fin n}
    (ha : a.val % 2 = 1) (hb : b.val % 2 = 0)
    (hi : a ≤ i ∧ i ≤ b) (hij : shiftedVisitAdj i j) :
    a ≤ j ∧ j ≤ b := by
  rcases hij with ⟨hiodd, hv⟩ | ⟨hjodd, hv⟩ <;> constructor
  all_goals omega

lemma odd_initial_arc_impossible {n : ℕ} {p : Pairing (n+2)}
    (hp : ∀ i, p.Occupied i)
    (hc : ∀ i, ReflTransGen p.visitWiring i 0)
    {a b : Fin (n+2)} (hab : p.Adj a b) (hlt : a < b) :
    a.val % 2 = 0 := by
  by_contra hna
  have ha : a.val % 2 = 1 := by omega
  have hpv := fully_matched_interval_even hp hab hlt
  rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero] at hpv
  have hb : b.val % 2 = 0 := by omega
  have hstable : ∀ {i j}, a ≤ i ∧ i ≤ b → p.visitWiring i j → a ≤ j ∧ j ≤ b := by
    intro i j hi hij
    rcases hij with hij | hij
    · exact adj_closed_interval hab hi hij
    · exact shiftedVisitAdj_closed_interval ha hb hi hij
  have hr := hc a
  have hreach : ∀ {j}, ReflTransGen p.visitWiring a j → a ≤ j ∧ j ≤ b := by
    intro j h
    induction h with
    | refl => exact ⟨le_rfl, hlt.le⟩
    | tail h hstep ih => exact hstable ih hstep
  have hz := (hreach hr).1
  change a.val ≤ 0 at hz
  omega

 

theorem single_component_visits_consecutive {n : ℕ} {p : Pairing (n+2)}
    (hp : ∀ i, p.Occupied i)
    (hc : ∀ i, ReflTransGen p.visitWiring i 0)
    {a b : Fin (n+2)} (hab : p.Adj a b) (hlt : a < b) :
    a.val % 2 = 0 ∧ b.val = a.val+1 := by
  have ha := odd_initial_arc_impossible hp hc hab hlt
  refine ⟨ha, ?_⟩
  by_contra hh
  have hgap : a.val + 1 < b.val := by omega
  let i : Fin (n+2) := ⟨a.val+1, hgap.trans b.isLt⟩
  have hai : a < i := by change a.val < a.val+1; omega
  have hib : i < b := by exact hgap
  obtain ⟨j,hj⟩ := hp i
  have hjmem := adj_interior hab hai hib hj
  have hodd : i.val % 2 = 1 := by dsimp [i]; omega
  have hne : i ≠ j := fun h => p.adj_irrefl i (h ▸ hj)
  rcases lt_or_gt_of_ne hne with hij | hji
  · have he := odd_initial_arc_impossible hp hc hj hij
    omega
  · have : a.val < j.val ∧ j.val < a.val+1 := ⟨hjmem.1, hji⟩
    omega

end Pairing
end
end CriticalStrip.Diagram

end OAI
