import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope3
noncomputable section
open Filter Topology
end
end RawSuccessInlineScope3

 

 

section RawSuccessInlineScope4

 
namespace IntervalResidueDiscrepancy
open Finset
open scoped BigOperators
noncomputable section

theorem prefix_bound (b q v : ℕ) (hq : 0 < q) :
    |(Nat.count (fun n => Nat.ModEq q n v) b : ℝ) - (b : ℝ)/q| ≤ 1 := by
  rw [Nat.count_modEq_card b hq v]
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hmod : ((b % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt b hq
  have hmod0 : (0:ℝ) ≤ ((b % q : ℕ) : ℝ) := by positivity
  have hid : ((b % q : ℕ) : ℝ) + (q : ℝ) * (b / q : ℕ) = b := by
    exact_mod_cast Nat.mod_add_div b q
  rw [abs_le]
  split_ifs <;> push_cast <;> constructor
  all_goals
    apply (mul_le_mul_iff_left₀ hqR).mp
    field_simp
    nlinarith

theorem interval_sum (A Y q v : ℕ) (hq : 0 < q) :
    |(∑ n ∈ Ico A (A+Y), if Nat.ModEq q n v then (1:ℝ) else 0) - (Y : ℝ)/q| ≤ 2 := by
  have h1 := prefix_bound (A+Y) q v hq
  have h0 := prefix_bound A q v hq
  rw [sum_Ico_eq_sub _ (by omega)]
  simp only [sum_boole, ← Nat.count_eq_card_filter_range]
  have heq : (Nat.count (fun n => Nat.ModEq q n v) (A+Y):ℝ) -
      Nat.count (fun n => Nat.ModEq q n v) A - (Y:ℝ)/q =
      ((Nat.count (fun n => Nat.ModEq q n v) (A+Y):ℝ) - ((A+Y:ℕ):ℝ)/q) -
      ((Nat.count (fun n => Nat.ModEq q n v) A:ℝ) - (A:ℝ)/q) := by push_cast; ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem interval_card (A Y q v : ℕ) (hq : 0 < q) :
    |(((Ico A (A+Y)).filter (fun n => Nat.ModEq q n v)).card : ℝ) - (Y : ℝ)/q| ≤ 2 := by
  simpa only [sum_boole] using interval_sum A Y q v hq

 

theorem class_and_dvd (A Y p a d : ℕ) (hp : 0 < p) (hd : 0 < d) (hpd : p.Coprime d) :
    |(∑ n ∈ (Ico A (A+Y)).filter (fun n => Nat.ModEq p n a),
        if d ∣ n then (1:ℝ) else 0) - (d:ℝ)⁻¹*((Y:ℝ)/p)| ≤ 2 := by
  let v := Nat.chineseRemainder hpd a 0
  have hm : ∀ n, (Nat.ModEq p n a ∧ d ∣ n) ↔ Nat.ModEq (p*d) n v := by
    intro n
    constructor
    · intro h
      exact Nat.chineseRemainder_modEq_unique hpd h.1 (Nat.modEq_zero_iff_dvd.mpr h.2)
    · intro h
      exact ⟨(h.of_mul_right d).trans v.property.1,
        Nat.modEq_zero_iff_dvd.mp ((h.of_mul_left p).trans v.property.2)⟩
  have hsum : (∑ n ∈ (Ico A (A+Y)).filter (fun n => Nat.ModEq p n a),
      if d ∣ n then (1:ℝ) else 0) =
      ∑ n ∈ Ico A (A+Y), if Nat.ModEq (p*d) n v then (1:ℝ) else 0 := by
    simp only [sum_filter, ← ite_and, hm]
  rw [hsum]
  convert interval_sum A Y (p*d) v (Nat.mul_pos hp hd) using 1
  push_cast
  congr 1
  ring

end
end IntervalResidueDiscrepancy

end RawSuccessInlineScope4

 

 

section RawSuccessInlineScope5
noncomputable section
open scoped BigOperators
open Finset
namespace UnitIntervalCounts

def units (A L W:ℕ) : Finset ℕ := (Ico A (A+L)).filter (fun n=>W.Coprime n)
def residues (W:ℕ) : Finset ℕ := (range W).filter (fun v=>W.Coprime v)

lemma coprime_mod (W n:ℕ) : W.Coprime (n%W) ↔ W.Coprime n := by
  simp only [Nat.coprime_iff_gcd_eq_one]
  rw [Nat.gcd_rec W n,Nat.gcd_comm (n%W) W]

lemma card_fibers (A L W:ℕ) (hW:0<W) :
    ((units A L W).card:ℝ) =
      ∑ v∈residues W, (((Ico A (A+L)).filter (fun n=>Nat.ModEq W n v)).card:ℝ) := by
  have hf:=Finset.sum_fiberwise_of_maps_to (s:=units A L W) (t:=residues W)
    (g:=fun n=>n%W) (fun n hn=> show n%W∈residues W by
      simp only [units,mem_filter] at hn
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt n hW),(coprime_mod W n).mpr hn.2⟩)
    (fun _=>(1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at hf
  rw [←hf]
  apply sum_congr rfl
  intro v hv
  congr 1
  have hv':v<W∧W.Coprime v := by simpa [residues] using hv
  congr 1
  ext n
  simp only [units,mem_filter]
  rw [Nat.ModEq, Nat.mod_eq_of_lt hv'.1]
  constructor
  · exact fun h=>⟨h.1.1,h.2⟩
  · intro h
    refine ⟨⟨h.1,?_⟩,h.2⟩
    apply (coprime_mod W n).mp
    rw [h.2]
    exact hv'.2

 

theorem discrepancy (A L W:ℕ) (hW:0<W) :
    |((units A L W).card:ℝ)-(L:ℝ)*W.totient/W| ≤ 2*W.totient := by
  rw [card_fibers A L W hW]
  have ht : (residues W).card=W.totient := (Nat.totient_eq_card_coprime W).symm
  have he : (∑ v∈residues W, (((Ico A (A+L)).filter (fun n=>Nat.ModEq W n v)).card:ℝ)) -
      (L:ℝ)*W.totient/W =
      ∑ v∈residues W, ((((Ico A (A+L)).filter (fun n=>Nat.ModEq W n v)).card:ℝ)-(L:ℝ)/W) := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul,ht]
    ring
  rw [he]
  calc
    _ ≤ ∑ v∈residues W, |((((Ico A (A+L)).filter (fun n=>Nat.ModEq W n v)).card:ℝ)-(L:ℝ)/W)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v∈residues W,(2:ℝ) := sum_le_sum (fun v _=>IntervalResidueDiscrepancy.interval_card A L W v hW)
    _ = _ := by rw [sum_const,nsmul_eq_mul,ht]; ring

lemma card_upper (A L W:ℕ) (hW:0<W) :
    ((units A L W).card:ℝ) ≤ W.totient*((L:ℝ)/W+2) := by
  have h:=(abs_le.mp (discrepancy A L W hW)).2
  linear_combination h

lemma card_lower (A L W:ℕ) (hW:0<W) (hL:4*W≤L) :
    (L:ℝ)*W.totient/(2*W) ≤ ((units A L W).card:ℝ) := by
  have h:=(abs_le.mp (discrepancy A L W hW)).1
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have hl:(4:ℝ)*W≤L:=by exact_mod_cast hL
  have ht:(0:ℝ)≤W.totient:=by positivity
  have hr:(4:ℝ)≤(L:ℝ)/W := (le_div_iff₀ hw).mpr hl
  have hid:(L:ℝ)*W.totient/W=((L:ℝ)/W)*W.totient:=by ring
  rw [hid] at h
  have hid':(L:ℝ)*W.totient/(2*W)=((L:ℝ)/W)*W.totient/2:=by ring
  rw [hid']
  nlinarith

end UnitIntervalCounts
end
end RawSuccessInlineScope5

 

 

section RawSuccessInlineScope6

 

namespace IntervalPrimeRootCount
open scoped BigOperators

 
theorem residue_card (A Y p v : ℕ) (_hp : 0 < p) :
    ((Finset.Ico A (A+Y)).filter (fun n => n % p = v)).card ≤ Y/p+1 := by
  classical
  let s := (Finset.Ico A (A+Y)).filter (fun n => n % p = v)
  have hbound : ∀ n ∈ s, (n-A)/p ∈ Finset.range (Y/p+1) := by
    intro n hn
    obtain ⟨hn,hmod⟩ := Finset.mem_filter.mp hn
    obtain ⟨hAn,hnY⟩ := Finset.mem_Ico.mp hn
    simp only [Finset.mem_range]
    have hs : n-A ≤ Y := by omega
    have hd := Nat.div_le_div_right hs (c := p)
    omega
  have hinj : Set.InjOn (fun n : ℕ => (n-A)/p) s := by
    intro n hn m hm he
    obtain ⟨hn,hmodn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hm,hmodm⟩ := Finset.mem_filter.mp hm
    obtain ⟨hAn,hnY⟩ := Finset.mem_Ico.mp hn
    obtain ⟨hAm,hmY⟩ := Finset.mem_Ico.mp hm
    have hmod : Nat.ModEq p n m := hmodn.trans hmodm.symm
    have hs : (n-A)%p = (m-A)%p := hmod.sub_right hAn hAm
    have hnq := Nat.mod_add_div (n-A) p
    have hmq := Nat.mod_add_div (m-A) p
    dsimp only at he
    rw [hs,he] at hnq
    omega
  calc
    s.card = (s.image (fun n => (n-A)/p)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (Y/p+1)).card := Finset.card_le_card (by
      intro q hq
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hq
      exact hbound n hn)
    _ = _ := Finset.card_range _

 
theorem zmod_card (A Y p : ℕ) (hp : 0 < p) (v : ZMod p) :
    ((Finset.Ico A (A+Y)).filter (fun n : ℕ => (n : ZMod p) = v)).card ≤ Y/p+1 := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  apply (Finset.card_le_card (t :=
    ((Finset.Ico A (A+Y)).filter (fun n => n % p = v.val))) ?_).trans
      (residue_card A Y p v.val hp)
  intro n hn
  obtain ⟨hn,hmod⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hn,?_⟩
  simpa only [ZMod.val_natCast] using congrArg ZMod.val hmod

 

theorem polynomial_root_card (A Y p : ℕ) [Fact p.Prime]
    (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    ((Finset.Ico A (A+Y)).filter (fun n : ℕ => f.eval (n : ZMod p) = 0)).card ≤
      f.natDegree*(Y/p+1) := by
  classical
  let roots := f.roots.toFinset
  have hcover : ((Finset.Ico A (A+Y)).filter (fun n : ℕ => f.eval (n : ZMod p) = 0)) ⊆
      roots.biUnion (fun v => (Finset.Ico A (A+Y)).filter (fun n : ℕ => (n : ZMod p) = v)) := by
    intro n hn
    obtain ⟨hn,hroot⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_biUnion.mpr
    refine ⟨(n : ZMod p),?_,Finset.mem_filter.mpr ⟨hn,rfl⟩⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr hroot)
  calc
    _ ≤ (roots.biUnion (fun v => (Finset.Ico A (A+Y)).filter
        (fun n : ℕ => (n : ZMod p) = v))).card := Finset.card_le_card hcover
    _ ≤ ∑ v ∈ roots, ((Finset.Ico A (A+Y)).filter
        (fun n : ℕ => (n : ZMod p) = v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ roots, (Y/p+1) := Finset.sum_le_sum (fun v hv =>
        zmod_card A Y p (Fact.out : p.Prime).pos v)
    _ = roots.card*(Y/p+1) := by simp
    _ ≤ f.natDegree*(Y/p+1) := Nat.mul_le_mul_right _
        ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f))

 

theorem harmonic_subset (P S : Finset ℕ) (hPS : S ⊆ P) (hP : P.Nonempty)
    (Y : ℕ) (hY : 0 < Y) (hbox : ∀ n ∈ P, Y ≤ n ∧ n < 2*Y) :
    (∑ n ∈ S, (n:ℝ)⁻¹) / (∑ n ∈ P, (n:ℝ)⁻¹) ≤ 2*(S.card:ℝ)/P.card := by
  have hn (n : ℕ) (hn : n ∈ P) : 0 < (n:ℝ) := by
    exact_mod_cast (hY.trans_le (hbox n hn).1)
  have hden : 0 < ∑ n ∈ P, (n:ℝ)⁻¹ :=
    Finset.sum_pos (fun n hn' => inv_pos.mpr (hn n hn')) hP
  have hcard : 0 < (P.card:ℝ) := by exact_mod_cast hP.card_pos
  have hnum : 0 ≤ ∑ n ∈ S, (n:ℝ)⁻¹ := Finset.sum_nonneg (fun n hn' => by positivity)
  have hupp : (Y:ℝ)*(∑ n ∈ S, (n:ℝ)⁻¹) ≤ S.card := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _n ∈ S, (1:ℝ) := Finset.sum_le_sum (by
        intro n hn'
        apply (mul_inv_le_iff₀ (hn n (hPS hn'))).mpr
        simpa only [one_mul] using (show (Y:ℝ) ≤ n from by
          exact_mod_cast (hbox n (hPS hn')).1))
      _ = _ := by simp
  have hlow : (P.card:ℝ) ≤ (2*Y)*(∑ n ∈ P, (n:ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _n ∈ P, (1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (by
        intro n hn'
        apply (le_mul_inv_iff₀ (hn n hn')).mpr
        simpa only [one_mul] using (show (n:ℝ) ≤ 2*Y from by
          exact_mod_cast (hbox n hn').2.le))
  rw [div_le_div_iff₀ hden hcard]
  calc
    _ ≤ (∑ n ∈ S, (n:ℝ)⁻¹)*((2*Y)*(∑ n ∈ P, (n:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left hlow hnum
    _ = 2*((Y:ℝ)*(∑ n ∈ S, (n:ℝ)⁻¹))*(∑ n ∈ P, (n:ℝ)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hupp (by norm_num)) hden.le

 

theorem harmonic_polynomial_roots (P : Finset ℕ) (hP : P.Nonempty)
    (Y p : ℕ) (hY : 0 < Y) [Fact p.Prime]
    (hbox : ∀ n ∈ P, Y ≤ n ∧ n < 2*Y)
    (f : Polynomial (ZMod p)) (hf : f ≠ 0) :
    (∑ n ∈ P.filter (fun n : ℕ => f.eval (n:ZMod p) = 0), (n:ℝ)⁻¹) /
      (∑ n ∈ P, (n:ℝ)⁻¹) ≤ 2*f.natDegree*(Y/p+1:ℕ)/P.card := by
  classical
  let S := P.filter (fun n : ℕ => f.eval (n:ZMod p) = 0)
  have hS : S.card ≤ f.natDegree*(Y/p+1) := by
    apply (Finset.card_le_card (t := (Finset.Ico Y (Y+Y)).filter
      (fun n : ℕ => f.eval (n:ZMod p) = 0)) ?_).trans
      (polynomial_root_card Y Y p f hf)
    intro n hn
    obtain ⟨hn,hr⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ?_,hr⟩
    obtain ⟨hl,hu⟩ := hbox n hn
    exact ⟨hl,by omega⟩
  calc
    _ ≤ 2*(S.card:ℝ)/P.card := harmonic_subset P S (Finset.filter_subset _ _) hP Y hY hbox
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hh : (S.card:ℝ) ≤ (f.natDegree:ℝ)*(Y/p+1:ℕ) := by exact_mod_cast hS
      nlinarith

 

theorem harmonic_integer_polynomial_divisors (P : Finset ℕ) (hP : P.Nonempty)
    (Y p : ℕ) (hY : 0 < Y) [Fact p.Prime]
    (hbox : ∀ n ∈ P, Y ≤ n ∧ n < 2*Y)
    (f : Polynomial ℤ) (hcoeff : ¬ (p:ℤ) ∣ f.leadingCoeff) :
    (∑ n ∈ P.filter (fun n : ℕ => (p:ℤ) ∣ f.eval (n:ℤ)), (n:ℝ)⁻¹) /
      (∑ n ∈ P, (n:ℝ)⁻¹) ≤ 2*f.natDegree*(Y/p+1:ℕ)/P.card := by
  classical
  let g := f.map (Int.castRingHom (ZMod p))
  have hg : g ≠ 0 := by
    intro hz
    have hc := congrArg (fun t : Polynomial (ZMod p) => t.coeff f.natDegree) hz
    have hc' : (f.leadingCoeff : ZMod p) = 0 := by
      simpa [g, Polynomial.coeff_natDegree] using hc
    exact hcoeff ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc')
  have hev (n : ℕ) : (g.eval (n:ZMod p) = 0) ↔ (p:ℤ) ∣ f.eval (n:ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [g, Polynomial.eval_map, Polynomial.eval₂_at_natCast]
  have hh := harmonic_polynomial_roots P hP Y p hY hbox g hg
  simp_rw [hev] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hd : (g.natDegree:ℝ) ≤ f.natDegree := by
    exact_mod_cast (show g.natDegree ≤ f.natDegree from Polynomial.natDegree_map_le)
  gcongr

end IntervalPrimeRootCount

end RawSuccessInlineScope6
end

end OAI
