import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.UniversalTables
import OAI.Combinatorics.SharpRamsey.Validation.ValidationSchedule

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def CoverInput (W : Finset (Projectivization K V))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ) (C b : ℝ)
    (z : Finset (Projectivization K V) × Finset (Projectivization K (Module.Dual K V))) : Prop :=
  z.1.Nonempty ∧ z.1 ⊆ W ∧ (N:ℝ) ≤ C*z.1.card ∧
  (W.card:ℝ) ≤ exp b*z.1.card ∧ z.2 ⊆ U ∧ z.2.card=t ∧
  (incidenceCount z.1 z.2:ℝ) ≤ (z.1.card:ℝ)*z.2.card/(10000*Nat.card K)

omit [Finite K] [FiniteDimensional K V] in
lemma coverInput_card (W : Finset (Projectivization K V))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ) (C b : ℝ) :
    (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      exp (((Fintype.card (Projectivization K V):ℝ)+
        Fintype.card (Projectivization K (Module.Dual K V)))*log 2) := by
  have hc := Fintype.card_subtype_le (CoverInput W U N t C b)
  have hc' : (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      (2:ℝ)^Fintype.card (Projectivization K V)*
      (2:ℝ)^Fintype.card (Projectivization K (Module.Dual K V)) := by
    simpa only [Fintype.card_prod,Fintype.card_finset,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (show (Fintype.card {x // CoverInput W U N t C b x}:ℝ) ≤ Fintype.card (Finset (Projectivization K V) × Finset (Projectivization K (Module.Dual K V))) by exact_mod_cast hc)
  apply hc'.trans_eq
  rw [add_mul,exp_add,exp_nat_mul,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma row_ratio_exp {x w b : ℝ} (_hx : 0<x) (hw : 0<w)
    (h : w ≤ exp b*x) (hrow : ℕ) : exp (-((hrow:ℝ)*b)) ≤ (x/w)^hrow := by
  have hh : exp (-b) ≤ x/w := by
    rw [le_div_iff₀ hw,exp_neg]
    apply (inv_mul_le_iff₀ (exp_pos b)).mpr
    nlinarith only [h]
  have hh' := pow_le_pow_left₀ (exp_pos (-b)).le hh hrow
  rwa [←exp_nat_mul, mul_neg] at hh'

theorem public_validation_cover {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : Finset (Projectivization K V)) (hW : W.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t ≤ U.card)
    (C b : ℝ) (hC : 1 ≤ C) (hb : 0 ≤ b)
    (hprod : (N:ℝ)*t ≤ 2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let M := 1000*C*q^(n+3)/N
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let a := (h:ℝ)*b+log 2+log (H+1)
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E ∈ caps, E ⊆ U ∧ (E.card:ℝ) ≤ M) ∧
      (∀ z, CoverInput W U N t C b z →
        ∃ E ∈ caps, (99/100:ℝ)*t ≤ (z.2∩E).card) ∧
      log ((caps.card:ℝ)+1) ≤ 2*a+log 3 := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let M := 1000*C*q^(n+3)/N
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let a := (h:ℝ)*b+log 2+log (H+1)
  have hq : 0<q := by change 0<(Nat.card K:ℝ); exact_mod_cast Nat.card_pos (α:=K)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have htr : (0:ℝ)<t := by exact_mod_cast ht
  have hw : (0:ℝ)<W.card := by exact_mod_cast card_pos.mpr hW
  have hut : (t:ℝ) ≤ U.card := by exact_mod_cast htu
  have hh : 0<h := scheduleLength_pos hq htr hut
  have hM : 0<M := by
    dsimp [M]
    have : 0<C := by linarith
    positivity
  have hH : 0 ≤ H := by dsimp [H]; exact mul_nonneg (by positivity) (log_nonneg (by norm_num))
  have ha₀ : 0 ≤ (h:ℝ)*b+log 2 := by positivity
  have hHP : 0 < H+1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; exact add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1 ≤ exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left hHP.le (one_le_exp_iff.mpr ha₀)
  let ι := {z // CoverInput W U N t C b z}
  let A : ι → (Fin h → Projectivization K V) → Prop := fun i =>
    implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M)
  have hprob : ∀ i, exp (-a) ≤ PublicTables.acceptProb (rowLaw W hW h) (A i) := by
    intro i
    obtain ⟨hx,hxw,hcap,hratio,htu',hct,hsp⟩ := i.2
    have hxr : (0:ℝ) < i.1.1.card := by exact_mod_cast card_pos.mpr hx
    have htt : i.1.2.Nonempty := card_pos.mp (by omega)
    have hsize := scheduleLength_size hq htr hut hNr hxr hC hcap hprod
      (pow_nonneg hq.le (n+3))
    have hsp' : (∑ y∈i.1.2,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass i.1.1 x) ≤
        (i.1.2.card:ℝ)/(10000*q) := by
      rw [uniform_incidence_sum]
      apply (div_le_iff₀ hxr).mpr
      apply hsp.trans_eq
      dsimp [q]
      ring
    have hg := projective_ideal_acceptance hdim i.1.1 hx U i.1.2 htt h hh M hM hsize hsp'
    change _ ≤ PublicTables.acceptProb (rowLaw W hW h)
      (implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M))
    rw [proposal_acceptance _ _ hx hW hxw]
    have hr := row_ratio_exp hxr hw hratio h
    have hprod' := mul_le_mul hr hg (by norm_num : (0:ℝ) ≤ 9/10) (by positivity)
    apply le_trans _ hprod'
    have he : exp (-((h:ℝ)*b+log 2))= exp (-((h:ℝ)*b))/2 := by
      rw [neg_add,exp_add,exp_neg (log 2),exp_log (by norm_num : (0:ℝ)<2)]
      ring
    calc
      exp (-a) ≤ exp (-((h:ℝ)*b+log 2)) := by
        apply exp_le_exp.mpr
        have hh' : 0 ≤ log (H+1) := log_nonneg (by linarith)
        dsimp [a]; linarith
      _ ≤ _ := by rw [he]; nlinarith [exp_pos (-((h:ℝ)*b))]
  obtain ⟨rows,hcard,hcovers,hlen⟩ := PublicTables.exists_cover (rowLaw W hW h) A a H ha
    (coverInput_card W U N t C b) hea hprob
  let goodrows := rows.filter (fun z => ((cap SharpLogRamsey.Incidence.Incident q U z).card:ℝ) ≤ M)
  let caps := goodrows.image (cap SharpLogRamsey.Incidence.Incident q U)
  refine ⟨caps,?_,?_,?_⟩
  · intro E hE
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hE
    exact ⟨filter_subset _ _,(mem_filter.mp hz).2⟩
  · intro z hz
    obtain ⟨r,hr,hacc⟩ := hcovers ⟨z,hz⟩
    have hg : GoodCap SharpLogRamsey.Incidence.Incident q U z.2 M r := hacc.2
    refine ⟨cap SharpLogRamsey.Incidence.Incident q U r,mem_image.mpr ⟨r,mem_filter.mpr ⟨hr,hg.1⟩,rfl⟩,?_⟩
    have hc := cap_capture hz.2.2.2.2.1 hg
    rw [hz.2.2.2.2.2.1] at hc
    nlinarith only [hc]
  · have hc : caps.card ≤ ⌈exp (2*a)⌉₊ :=
      (card_image_le.trans (card_filter_le _ _)).trans hcard
    apply le_trans _ hlen
    apply log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hc 1

end
end SharpLogRamsey.Validation

end

end OAI
