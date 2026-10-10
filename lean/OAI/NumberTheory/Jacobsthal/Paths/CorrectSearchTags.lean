import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinRationalList
import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinRepresentatives

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ActualBinOwners

open _root_.Erdos970.Set _root_.Erdos970.Finset
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

def eligible (Y w Cs : ℝ) (q : ℚ) : Prop :=
  (q.den:ℝ) ≤ w^Cs ∧ (q.num.natAbs:ℝ) ≤ Y*w^(Cs+2)

noncomputable def ownerCandidates (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) : Finset ℚ :=
  sourceRationalList (primeBin R xi) a (Y*w^2) (w^Cs) 1 (1-eta)

theorem mem_ownerCandidates {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (a : ℕ → ℤ) (q : ℚ) :
    q ∈ ownerCandidates Y w Cs eta R xi a ↔ eligible Y w Cs q ∧
      (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ) := by
  have hw0 : 0 < w := by linarith
  rw [ownerCandidates,mem_sourceRationalList _ _ (by positivity) (Real.rpow_nonneg hw0.le Cs)]
  have he : Y*w^2*w^Cs = Y*w^(Cs+2) := by
    rw [Real.rpow_add hw0,Real.rpow_ofNat]
    ring
  simp only [one_pow,mul_one,he,eligible]
  tauto

noncomputable def chooseOwner (C : Finset ℚ) : Option ℚ :=
  if h : C.Nonempty then some (C.min' h) else none

noncomputable def owner (Y w Cs eta R xi : ℝ) (a : ℕ → ℤ) : Option ℚ :=
  chooseOwner (ownerCandidates Y w Cs eta R xi a)

theorem chooseOwner_mem (C : Finset ℚ) {q : ℚ} (h : chooseOwner C = some q) : q ∈ C := by
  by_cases hC : C.Nonempty
  · rw [chooseOwner,dite_eq_left hC] at h
    have he := Option.some.inj h
    exact he ▸ Finset.min'_mem C hC
  · simp [chooseOwner,hC] at h

theorem chooseOwner_exists_iff (C : Finset ℚ) : (∃ q,chooseOwner C = some q) ↔ C.Nonempty := by
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q,chooseOwner_mem C hq⟩
  · intro hC
    exact ⟨C.min' hC,by simp [chooseOwner,hC]⟩

theorem chooseOwner_of_unique (C : Finset ℚ) (q : ℚ) (hq : q ∈ C)
    (hunique : ∀ r ∈ C,r = q) : chooseOwner C = some q := by
  have hC : C.Nonempty := ⟨q,hq⟩
  have hm := hunique (C.min' hC) (Finset.min'_mem C hC)
  simp [chooseOwner,hC,hm]

theorem actual_owner_witness {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (a : ℕ → ℤ) {q : ℚ} (ho : owner Y w Cs eta R xi a = some q) :
    eligible Y w Cs q ∧ (1-eta)*((primeBin R xi).card:ℝ) ≤
      (((primeBin R xi).filter (aligns a q)).card:ℝ) :=
  (mem_ownerCandidates hY hw a q).mp (chooseOwner_mem _ ho)

theorem actual_owner_exists {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w) (a : ℕ → ℤ) :
    (∃ q,owner Y w Cs eta R xi a = some q) ↔
      ∃ q,eligible Y w Cs q ∧ (1-eta)*((primeBin R xi).card:ℝ) ≤
        (((primeBin R xi).filter (aligns a q)).card:ℝ) := by
  rw [owner,chooseOwner_exists_iff]
  constructor
  · rintro ⟨q,hq⟩
    exact ⟨q,(mem_ownerCandidates hY hw a q).mp hq⟩
  · rintro ⟨q,hq⟩
    exact ⟨q,(mem_ownerCandidates hY hw a q).mpr hq⟩

end NumberTheoryLean.ActualBinOwners

end

section

namespace NumberTheoryLean.FiniteFirstTag


structure Tag (n : ℕ) where
  index : ℕ
  bin : Fin n
  rational : ℚ
  deriving DecidableEq

def firstTagFrom {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) : ℕ → List ℕ → Option (Tag n)
  | _,[] => none
  | k,p::ps => match F p with
      | none => firstTagFrom F (k+1) ps
      | some (b,q) => some ⟨k,b,q⟩

def firstTag {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (ps : List ℕ) : Option (Tag n) :=
  firstTagFrom F 0 ps

theorem firstTagFrom_witness {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps : List ℕ)
    {t : Tag n} (ht : firstTagFrom F k ps = some t) :
    ∃ pre : List ℕ,∃ p : ℕ,∃ tail : List ℕ, ps = pre++p::tail ∧
      t.index = k+pre.length ∧ F p = some (t.bin,t.rational) ∧ ∀ q ∈ pre,F q = none := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom] at ht
  | cons p ps ih =>
    cases hp : F p with
    | none =>
      rw [firstTagFrom,hp] at ht
      obtain ⟨pre,q,tail,hps,hindex,hq,hpre⟩ := ih (k+1) ht
      refine ⟨p::pre,q,tail,?_,?_,hq,?_⟩
      · rw [List.cons_append,hps]
      · simp only [List.length_cons]
        omega
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hp
        · exact hpre r hr
    | some bq =>
      rcases bq with ⟨b,q⟩
      rw [firstTagFrom,hp] at ht
      have he : (⟨k,b,q⟩ : Tag n) = t := Option.some.inj ht
      subst t
      exact ⟨[],p,ps,rfl,by simp,hp,by simp⟩

theorem firstTagFrom_append {n : ℕ} (F : ℕ → Option (Fin n × ℚ)) (k : ℕ) (ps qs : List ℕ)
    {t : Tag n} (ht : firstTagFrom F k ps = some t) : firstTagFrom F k (ps++qs) = some t := by
  induction ps generalizing k with
  | nil => simp [firstTagFrom] at ht
  | cons p ps ih =>
    cases hp : F p with
    | none =>
      simp only [List.cons_append,firstTagFrom,hp] at ht ⊢
      exact ih (k+1) ht
    | some bq =>
      simpa only [List.cons_append,firstTagFrom,hp] using ht

theorem firstTagFrom_map_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (k : ℕ) (ps qs : List ℕ) (hmap : ps.map F = qs.map F) :
    firstTagFrom F k ps = firstTagFrom F k qs := by
  induction ps generalizing k qs with
  | nil =>
    have hq : qs = [] := List.map_eq_nil_iff.mp hmap.symm
    subst qs
    rfl
  | cons p ps ih =>
    cases qs with
    | nil => simp at hmap
    | cons q qs =>
      have hh := List.cons.inj hmap
      simp only [firstTagFrom,hh.1]
      cases hq : F q with
      | none => exact ih (k+1) qs hh.2
      | some bq => rfl

theorem tag_replacement_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (pre tail : List ℕ) (p q : ℕ) (hpq : F p = F q) :
    firstTag F (pre++p::tail) = firstTag F (pre++q::tail) := by
  apply firstTagFrom_map_invariant
  simp only [List.map_append,List.map_cons,hpq]

theorem tag_prefix_invariant {n : ℕ} (F : ℕ → Option (Fin n × ℚ))
    (ps qs : List ℕ) (hmap : ps.map F = qs.map F) (k : ℕ) :
    firstTag F (ps.take k) = firstTag F (qs.take k) := by
  apply firstTagFrom_map_invariant
  rw [List.map_take,List.map_take,hmap]

end NumberTheoryLean.FiniteFirstTag

end

section

namespace NumberTheoryLean.OwnerUniquenessFinite
open ActualBinOwners ErdosInverseAlignment ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable

theorem common_dense_lower (P : Finset ℕ) (a : ℕ → ℤ) (q r : ℚ) (eta : ℝ)
    (hq : (1-eta)*(P.card:ℝ) ≤ ((P.filter (aligns a q)).card:ℝ))
    (hr : (1-eta)*(P.card:ℝ) ≤ ((P.filter (aligns a r)).card:ℝ)) :
    (1-2*eta)*(P.card:ℝ) ≤ ((commonAligners P a q r).card:ℝ) := by
  let A := P.filter (aligns a q)
  let B := P.filter (aligns a r)
  have hsub : A ∪ B ⊆ P := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hu := Finset.card_le_card hsub
  have hi : A ∩ B=commonAligners P a q r := by ext p; simp [A,B,commonAligners]; tauto
  have hh := Finset.card_union_add_card_inter A B
  rw [hi] at hh
  have hhr : ((A ∪ B).card:ℝ)+((commonAligners P a q r).card:ℝ)=(A.card:ℝ)+(B.card:ℝ) := by exact_mod_cast hh
  have hur : ((A ∪ B).card:ℝ) ≤ (P.card:ℝ) := by exact_mod_cast hu
  change (1-eta)*(P.card:ℝ) ≤ (A.card:ℝ) at hq
  change (1-eta)*(P.card:ℝ) ≤ (B.card:ℝ) at hr
  nlinarith

theorem eligible_determinant_height {Y w Cs : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (q r : ℚ) (hq : eligible Y w Cs q) (hr : eligible Y w Cs r) :
    ((determinant q r).natAbs:ℝ) ≤ 2*Y*w^(2*Cs+2) := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have hnat : (determinant q r).natAbs ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
    simpa only [determinant,Int.natAbs_mul,Int.natAbs_natCast] using
      (Int.natAbs_sub_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ)))
  have hh : ((determinant q r).natAbs:ℝ) ≤
      (q.num.natAbs:ℝ)*(r.den:ℝ)+(r.num.natAbs:ℝ)*(q.den:ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ _ := hh
    _ ≤ (Y*w^(Cs+2))*w^Cs+(Y*w^(Cs+2))*w^Cs :=
      add_le_add (mul_le_mul hq.2 hr.1 (Nat.cast_nonneg _) (by positivity))
        (mul_le_mul hr.2 hq.1 (Nat.cast_nonneg _) (by positivity))
    _ = 2*Y*(w^(Cs+2)*w^Cs) := by ring
    _ = _ := by rw [← Real.rpow_add hw0]; congr 2; ring

theorem owner_candidates_unique {Y w Cs eta R xi C : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ)
    (hheight : 2*Y*w^(2*Cs+2) ≤ R^C)
    (hcount : C < (1-2*eta)*((primeBin R xi).card:ℝ)) :
    ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  intro q hq r hr
  by_contra hne
  have hq' := (mem_ownerCandidates hY hw a q).mp hq
  have hr' := (mem_ownerCandidates hY hw a r).mp hr
  have hd := (eligible_determinant_height hY hw q r hq'.1 hr'.1).trans hheight
  have hP : ∀ p ∈ primeBin R xi,p.Prime := fun p hp =>
    ((mem_primeBin (zero_lt_one.trans hR).le hxi p).mp hp).1
  have hlarge : ∀ p ∈ primeBin R xi,R^(1:ℝ) ≤ (p:ℝ) := by
    intro p hp
    rw [Real.rpow_one]
    exact ((mem_primeBin (zero_lt_one.trans hR).le hxi p).mp hp).2.1.le
  have hu := common_primes_power_height_bound (primeBin R xi) a hne hP hR (by norm_num : (0:ℝ)<1) hlarge hd
  rw [div_one] at hu
  exact (not_le_of_gt hcount) ((common_dense_lower (primeBin R xi) a q r eta hq'.2 hr'.2).trans hu)

theorem owner_unique_of_exp_height {Y w Cs eta R xi H : ℝ} (hY : 0 ≤ Y) (hw : 1 < w)
    (hR : 1 < R) (hxi : 0 ≤ xi) (a : ℕ → ℤ)
    (hheight : 2*Y*w^(2*Cs+2) ≤ Real.exp H)
    (hcount : H < (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R) :
    ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  apply owner_candidates_unique hY hw hR hxi a (C := H/Real.log R)
  · have he : R^(H/Real.log R)=Real.exp H := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hR)]
      congr 1
      field_simp [(Real.log_pos hR).ne']
    rw [he]
    exact hheight
  · exact (div_lt_iff₀ (Real.log_pos hR)).mpr hcount
end NumberTheoryLean.OwnerUniquenessFinite

end

section

namespace NumberTheoryLean.OwnerSearchBounds

theorem height_exp_square {Y w Cs : ℝ} (_hY : 0 ≤ Y) (hw : 1 ≤ w) (hCs : 0 ≤ Cs)
    (hlarge : 2*Cs+3 ≤ w) (hYup : Y ≤ Real.exp (w^2)) :
    2*Y*w^(2*Cs+2) ≤ Real.exp (2*w^2) := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hA : 0 ≤ 2*Cs+2 := by linarith
  have hlog : Real.log w ≤ w := (Real.log_le_sub_one_of_pos hw0).trans (by linarith)
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hh := mul_le_mul_of_nonneg_left hlog hA
  have hbound : w^2+(2*Cs+2)*Real.log w+Real.log 2 ≤ 2*w^2 := by nlinarith
  have he : Real.exp (w^2+(2*Cs+2)*Real.log w+Real.log 2)=2*Real.exp (w^2)*w^(2*Cs+2) := by
    rw [Real.exp_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),Real.rpow_def_of_pos hw0]
    rw [mul_comm (2*Cs+2) (Real.log w)]
    ring
  calc
    _ ≤ 2*Real.exp (w^2)*w^(2*Cs+2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hYup (by norm_num)) (Real.rpow_nonneg hw0.le _)
    _ = Real.exp (w^2+(2*Cs+2)*Real.log w+Real.log 2) := he.symm
    _ ≤ _ := Real.exp_le_exp.mpr hbound

theorem search_ge_fourth {w R : ℝ} (hw : 1 ≤ w) (hp : 4 ≤ w^((1/4:ℝ)))
    (hR : w^(w^((1/4:ℝ))) ≤ R) : w^4 ≤ R := by
  have hh := Real.rpow_le_rpow_of_exponent_le hw hp
  have hh' : w^4 ≤ w^(w^((1/4:ℝ))) := by simpa only [Real.rpow_ofNat] using hh
  exact hh'.trans hR

theorem le_fourth {w : ℝ} (hw : 1 ≤ w) : w ≤ w^4 := by
  have h2 : 1 ≤ w^2 := by nlinarith
  nlinarith [sq_nonneg (w^2-1)]

theorem quadratic_lt_scaled_fourth {beta w : ℝ} (hb : 0 < beta) (hw : 1 ≤ w)
    (hlarge : 4/beta ≤ w) : 2*w^2 < beta*w^4 := by
  have hw0 : 0 < w := zero_lt_one.trans_le hw
  have hbw : 4 ≤ beta*w := by nlinarith [(div_le_iff₀ hb).mp hlarge]
  have hb2 : 4 ≤ beta*w^2 := by
    have hh := mul_le_mul_of_nonneg_right hbw hw0.le
    nlinarith
  have hh := mul_pos (show 0 < beta*w^2-2 by linarith) (sq_pos_of_pos hw0)
  nlinarith
end NumberTheoryLean.OwnerSearchBounds

end

section

namespace NumberTheoryLean.UniformSearchOwner
open _root_.Filter _root_.Erdos970.Filter ActualBinOwners OwnerSearchBounds OwnerUniquenessFinite
open ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

theorem uniform_search_owner_unique {Cs eta theta : ℝ} (hCs : 0 ≤ Cs)
    (heta : eta < 1/2) (htheta : 0 < theta) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ Y R xi : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      w^(w^((1/4:ℝ))) ≤ R → theta ≤ xi → xi ≤ 1 → ∀ a : ℕ → ℤ,
      ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r := by
  let beta : ℝ := (1-2*eta)*theta/4
  have hcoef : 0 < 1-2*eta := by linarith
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp (uniform_prime_bin_count htheta)
  have hquarter : ∀ᶠ w : ℝ in atTop,4 ≤ w^((1/4:ℝ)) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).eventually_ge_atTop 4
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop R₀,
    eventually_ge_atTop (2*Cs+3),eventually_ge_atTop (4/beta),hquarter] with w hw2 hwR hwCs hwBeta hwPow
  refine ⟨hw2,?_⟩
  intro Y R xi hY hYup hsearch hxi hxi1 a
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 < w := by linarith
  have hfour := search_ge_fourth hw1 hwPow hsearch
  have hwR' : w ≤ R := (le_fourth hw1).trans hfour
  have hcount := hR₀ R (hwR.trans hwR')
  have hR1 : 1 < R := by linarith [hcount.1]
  have hR0 : 0 < R := zero_lt_one.trans hR1
  have hlog : 0 < Real.log R := Real.log_pos hR1
  have hc := (hcount.2 xi hxi hxi1).1
  have hcm : xi*R/4 ≤ ((primeBin R xi).card:ℝ)*Real.log R := by
    have hh := (div_le_iff₀ (show 0 < 4*Real.log R by positivity)).mp hc
    nlinarith
  have hlower : beta*R ≤ (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R := by
    calc
      beta*R=(1-2*eta)*(theta*R/4) := by dsimp [beta]; ring
      _ ≤ (1-2*eta)*(xi*R/4) := by gcongr
      _ ≤ (1-2*eta)*(((primeBin R xi).card:ℝ)*Real.log R) :=
        mul_le_mul_of_nonneg_left hcm hcoef.le
      _ = _ := by ring
  have hsize : 2*w^2 < (1-2*eta)*((primeBin R xi).card:ℝ)*Real.log R :=
    (quadratic_lt_scaled_fourth hbeta hw1 hwBeta).trans_le
      ((mul_le_mul_of_nonneg_left hfour hbeta.le).trans hlower)
  exact owner_unique_of_exp_height hY (by linarith) hR1 (htheta.le.trans hxi) a
    (height_exp_square hY hw1 hCs hwCs hYup) hsize

theorem owner_eq_of_unique {Y w Cs eta R xi : ℝ} (hY : 0 ≤ Y) (hw : 1 < w) (a : ℕ → ℤ)
    (hu : ∀ q ∈ ownerCandidates Y w Cs eta R xi a,∀ r ∈ ownerCandidates Y w Cs eta R xi a,q=r)
    (q : ℚ) (he : eligible Y w Cs q)
    (hd : (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ)) :
    owner Y w Cs eta R xi a=some q := by
  have hq := (mem_ownerCandidates hY hw a q).mpr ⟨he,hd⟩
  exact chooseOwner_of_unique _ q hq (fun r hr => hu r hr q hq)
end NumberTheoryLean.UniformSearchOwner

end

section

namespace NumberTheoryLean.ActualSourceTags

open _root_.Erdos970.Set _root_.Erdos970.Finset
open ActualBinOwners FiniteFirstTag PrimeBinRepresentatives ErdosInversePrimeBin ErdosInverseAlignment
attribute [local instance] Classical.propDecidable

def searchBin (w R : ℝ) : Prop := w^((1/4:ℝ)) ≤ leftExponent w R

noncomputable def tagCandidate {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) : Option (Fin n × ℚ) :=
  if p ∈ primeBin (lower (label p)) (width (label p)) ∧ searchBin w (lower (label p)) then
    match owner Y w Cs eta (lower (label p)) (width (label p)) a with
    | none => none
    | some q => if aligns a q p then some (label p,q) else none
  else none

theorem candidate_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q)) :
    b = label p ∧ p ∈ primeBin (lower (label p)) (width (label p)) ∧
      searchBin w (lower (label p)) ∧ owner Y w Cs eta (lower (label p)) (width (label p)) a = some q ∧
      aligns a q p := by
  by_cases hgood : p ∈ primeBin (lower (label p)) (width (label p)) ∧ searchBin w (lower (label p))
  · rw [tagCandidate,ite_eq_left hgood] at ht
    cases ho : owner Y w Cs eta (lower (label p)) (width (label p)) a with
    | none => simp [ho] at ht
    | some r =>
      rw [ho] at ht
      dsimp only at ht
      by_cases ha : aligns a r p
      · rw [ite_eq_left ha] at ht
        have hh := Prod.mk.inj (Option.some.inj ht)
        rcases hh with ⟨hb,hq⟩
        subst r
        exact ⟨hb.symm,hgood.1,hgood.2,rfl,ha⟩
      · simp [ha] at ht
  · simp [tagCandidate,hgood] at ht

theorem candidate_of_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) (q : ℚ)
    (hp : p ∈ primeBin (lower (label p)) (width (label p))) (hs : searchBin w (lower (label p)))
    (ho : owner Y w Cs eta (lower (label p)) (width (label p)) a = some q) (ha : aligns a q p) :
    tagCandidate Y w Cs eta lower width label a p = some (label p,q) := by
  simp only [tagCandidate,hp,hs,and_self,ite_true,ho,ha]

noncomputable def sourceTag {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) : Option (Tag n) :=
  firstTag (tagCandidate Y w Cs eta lower width label a) ps

theorem sourceTag_witness {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (ps : List ℕ) {t : Tag n}
    (ht : sourceTag Y w Cs eta lower width label a ps = some t) :
    ∃ pre : List ℕ,∃ p : ℕ,∃ tail : List ℕ, ps = pre++p::tail ∧ t.index = pre.length ∧
      t.bin = label p ∧ p ∈ primeBin (lower (label p)) (width (label p)) ∧
      searchBin w (lower (label p)) ∧ owner Y w Cs eta (lower (label p)) (width (label p)) a = some t.rational ∧
      aligns a t.rational p ∧ ∀ q ∈ pre,tagCandidate Y w Cs eta lower width label a q = none := by
  obtain ⟨pre,p,tail,hps,hindex,hp,hpre⟩ := firstTagFrom_witness
    (tagCandidate Y w Cs eta lower width label a) 0 ps ht
  have hc := candidate_witness Y w Cs eta lower width label a p hp
  exact ⟨pre,p,tail,hps,by simpa only [zero_add] using hindex,hc.1,hc.2.1,hc.2.2.1,
    hc.2.2.2.1,hc.2.2.2.2,hpre⟩

theorem candidate_replacement {n : ℕ} (Y w Cs eta : ℝ) (lower width : Fin n → ℝ)
    (label : ℕ → Fin n) (a : ℕ → ℤ) (p p' : ℕ) {b : Fin n} {q : ℚ}
    (ht : tagCandidate Y w Cs eta lower width label a p = some (b,q))
    (hlabel : label p' = label p)
    (hp' : p' ∈ primeBin (lower (label p')) (width (label p'))) (ha : aligns a q p') :
    tagCandidate Y w Cs eta lower width label a p' = tagCandidate Y w Cs eta lower width label a p := by
  have hc := candidate_witness Y w Cs eta lower width label a p ht
  have hs : searchBin w (lower (label p')) := by rw [hlabel]; exact hc.2.2.1
  have ho : owner Y w Cs eta (lower (label p')) (width (label p')) a = some q := by
    rw [hlabel]
    exact hc.2.2.2.1
  rw [candidate_of_witness Y w Cs eta lower width label a p' q hp' hs ho ha,ht,hlabel,← hc.1]

end NumberTheoryLean.ActualSourceTags

end

section

namespace NumberTheoryLean.CorrectSearchTags
open _root_.Filter _root_.Erdos970.Filter ActualBinOwners ActualSourceTags UniformSearchOwner PrimeBinRepresentatives
open ErdosInverseAlignment ErdosInversePrimeBin
attribute [local instance] Classical.propDecidable

theorem searchBin_lower {w R : ℝ} (hw : 1 < w) (hR : 0 < R) (hs : searchBin w R) :
    w^(w^((1/4:ℝ))) ≤ R := by
  have hlog : 0 < Real.log w := Real.log_pos hw
  have hh := (le_div_iff₀ hlog).mp hs
  calc
    _ = Real.exp (Real.log w*w^((1/4:ℝ))) := Real.rpow_def_of_pos (zero_lt_one.trans hw) _
    _ ≤ Real.exp (Real.log R) := Real.exp_le_exp.mpr (by nlinarith only [hh])
    _ = R := Real.exp_log hR

theorem uniform_correct_owner {Cs eta theta : ℝ} (hCs : 0 ≤ Cs)
    (heta : eta < 1/2) (htheta : 0 < theta) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ Y R xi : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      0 < R → searchBin w R → theta ≤ xi → xi ≤ 1 → ∀ (a : ℕ → ℤ) (q : ℚ),
      eligible Y w Cs q →
      (1-eta)*((primeBin R xi).card:ℝ) ≤ (((primeBin R xi).filter (aligns a q)).card:ℝ) →
      owner Y w Cs eta R xi a=some q := by
  filter_upwards [uniform_search_owner_unique hCs heta htheta] with w hw
  refine ⟨hw.1,?_⟩
  intro Y R xi hY hYup hR hs hxi hxi1 a q he hd
  have hw1 : 1 < w := by linarith [hw.1]
  exact owner_eq_of_unique hY hw1 a
    (hw.2 Y R xi hY hYup (searchBin_lower hw1 hR hs) hxi hxi1 a) q he hd

theorem uniform_correct_search_candidate {Cs eta theta : ℝ} (hCs : 0 ≤ Cs)
    (heta : eta < 1/2) (htheta : 0 < theta) :
    ∀ᶠ w : ℝ in atTop,2 ≤ w ∧ ∀ Y : ℝ,0 ≤ Y → Y ≤ Real.exp (w^2) →
      ∀ (n : ℕ) (lower width : Fin n → ℝ) (label : ℕ → Fin n) (a : ℕ → ℤ) (p : ℕ) (q : ℚ),
      0 < lower (label p) → searchBin w (lower (label p)) →
      theta ≤ width (label p) → width (label p) ≤ 1 →
      p ∈ primeBin (lower (label p)) (width (label p)) → eligible Y w Cs q →
      (1-eta)*((primeBin (lower (label p)) (width (label p))).card:ℝ) ≤
        (((primeBin (lower (label p)) (width (label p))).filter (aligns a q)).card:ℝ) →
      aligns a q p → tagCandidate Y w Cs eta lower width label a p=some (label p,q) := by
  filter_upwards [uniform_correct_owner hCs heta htheta] with w hw
  refine ⟨hw.1,?_⟩
  intro Y hY hYup n lower width label a p q hlo hs hwidth hwidth1 hp he hd ha
  have ho := hw.2 Y (lower (label p)) (width (label p)) hY hYup hlo hs hwidth hwidth1 a q he hd
  exact candidate_of_witness Y w Cs eta lower width label a p q hp hs ho ha
end NumberTheoryLean.CorrectSearchTags

end

end Erdos970

end OAI
