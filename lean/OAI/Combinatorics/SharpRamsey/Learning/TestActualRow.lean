import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.TestRowBounds

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory LearningRow
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestActualRow_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestActualRow_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedTestActualRow_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

abbrev inc (H : Projectivization K (Module.Dual K V)) (x : Projectivization K V) : Prop :=
  x.submodule≤LinearMap.ker H.rep

lemma pencil_inter_count (Z : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V) :
    (pencil x∩Z).card=(Z.filter (fun H => inc H x)).card := by
  congr 1
  ext H
  simp only [pencil,inc,mem_filter,mem_univ,true_and,mem_inter]
  tauto

lemma pencil_degree (Z : Finset (Projectivization K (Module.Dual K V))) (x : Projectivization K V) :
    PencilContrast.degree Incidence.Incident Z x=((pencil x∩Z).card:ℝ) := by
  rw [pencil_inter_count]
  simp only [PencilContrast.degree,Incidence.incident_iff_submodule,inc,card_filter,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

def rowTest (S : Finset (Projectivization K V)) (O : Projectivization K V→Finset (Projectivization K V))
    (E : Finset (Projectivization K (Module.Dual K V))) (b : Projectivization K V→ℝ)
    {R : ℕ} (ω : Schedule S R) : Finset (Projectivization K V) :=
  test (sample S ω) (fun x => score S (O x) (pencil x) inc (b x) ω)
    (emptySet S E inc ω).card (Nat.card K)

theorem geometric_row_probability
    (n R p h : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty) (hDa : Ds⊆Da)
    (O : Projectivization K V→Finset (Projectivization K V))
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (f : Projectivization K V→ℝ) (hf : ∀ x,f x≤1/25)
    (B C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-f x))*((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (O x) x c L (pencil x\E) (f x) B C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (O x) x c L (pencil x\E) (f x) B T a) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
        (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-Real.exp (-μmean/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω |
        ((sample S ω).card:ℝ)≤2*μmean ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤
          (S∩rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card ∧
        ((rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card:ℝ)≤
          2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin} := by
  dsimp only
  let q : ℝ := Nat.card K
  let b : Projectivization K V→ℝ := fun x => Real.exp (-(L:ℝ)*(1-f x))
  let μ := PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)
  let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
  let z := fun ω : Schedule S R => ((emptySet S E inc ω).card:ℝ)
  let zx := fun (ω : Schedule S R) x => ((pencil x∩emptySet S E inc ω).card:ℝ)
  let typ := fun (ω : Schedule S R) x => score S (O x) (pencil x\E) inc (b x) ω
  let full := fun (ω : Schedule S R) x => score S (O x) (pencil x) inc (b x) ω
  let t := zmin/(10*q)
  let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
  let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
  let FS := fun x => {ω : Schedule S R | x∉Ds ∧ x∉sample S ω ∧ t≤|typ ω x|}
  let FA := fun x => {ω : Schedule S R | x∉Da ∧ x∉sample S ω ∧ t≤|typ ω x|}
  let G := {ω : Schedule S R | zmin≤z ω ∧
    (∑ H∈emptySet S E inc ω,(q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤(δ+u)*z ω}
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have ht : 0<t := by dsimp [t]; positivity
  have hB0 : 0≤B := (Real.exp_pos _).le.trans hB
  have hd : Module.finrank K V≤n+2+1 := by omega
  have hgood := actual_empty_good S E E₀ R inc (L*c)
    (fun H => (q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ)) ((L:ℝ)*R) bE δ u zmin W
    hE₀ hE₀E (by positivity) hδ hu hzmin (by intro H _; positivity)
    (by intro H _; rw [NNReal.coe_mul,hc]; ring) hsmall hW hZ
  have hfs : ∀ x∈S,μ.real (FS x)≤εs := by
    intro x _
    by_cases hx : x∈Ds
    · have he : FS x=∅ := by ext ω; simp [FS,hx]
      rw [he,measureReal_empty]
      dsimp [εs]
      positivity
    · have hh := score_second_tail (n+2) R hd S (O x) x c L E (f x) B C
        (by linarith [hf x]) hB0 hC (by linarith) (by omega) T a (hs x hx) t ht
      exact (measureReal_mono (h₂:=measure_ne_top μ _) (fun ω hω => hω.2)).trans hh
  have hfa : ∀ x,μ.real (FA x)≤εa := by
    intro x
    by_cases hx : x∈Da
    · have he : FA x=∅ := by ext ω; simp [FA,hx]
      rw [he,measureReal_empty]
      dsimp [εa]
      have hBp : 0≤B^p := pow_nonneg hB0 p
      positivity
    · have hh := score_high_tail (n+2) R p h (by omega) (by omega) hd S (O x) x c L E
        (f x) B (hf x) hp hpe hL hR hB T a (ha x hx) t ht
      exact (measureReal_mono (h₂:=measure_ne_top μ _) (fun ω hω => hω.2)).trans hh
  have halpha (x : Projectivization K V) := alpha_bounds (L:ℝ) (f x) R L.coe_nonneg (hf x) hα
  have herrors : ∀ ω∈G,∀ x,x∉Ds → x∉sample S ω →
      |(full ω x-typ ω x)-(1-b x)^R*zx ω x|≤z ω/(100*q) := by
    intro ω hω x hx _
    exact (exceptional_error S (O x) (pencil x) E inc (b x) ω
      (halpha x).1 (halpha x).2.1).trans ((herror x hx).trans
      (div_le_div_of_nonneg_right hω.1 (by positivity)))
  have htypS : ∀ ω∈G,∀ x∈S,x∉Ds → x∉sample S ω → ω∉FS x → |typ ω x|≤z ω/(10*q) := by
    intro ω hω x _ hx hsample hFS
    have hh : |typ ω x|<t := lt_of_not_ge (fun hh => hFS ⟨hx,hsample,hh⟩)
    exact hh.le.trans (div_le_div_of_nonneg_right hω.1 (by positivity))
  have htypA : ∀ ω∈G,∀ x,x∉Da → x∉sample S ω → ω∉FA x → |typ ω x|≤z ω/(10*q) := by
    intro ω hω x hx hsample hFA
    have hh : |typ ω x|<t := lt_of_not_ge (fun hh => hFA ⟨hx,hsample,hh⟩)
    exact hh.le.trans (div_le_div_of_nonneg_right hω.1 (by positivity))
  have hZnonempty (ω : Schedule S R) (hω : ω∈G) : (emptySet S E inc ω).Nonempty := by
    apply card_pos.mp
    have hh : (0:ℝ)<(emptySet S E inc ω).card := hzmin.trans_le hω.1
    exact_mod_cast hh
  have hes : ∀ ω∈G,((S.filter (fun x => z ω/(10*q)<zx ω x)).card:ℝ)≤10*(δ+u)*(S.card:ℝ) := by
    intro ω hω
    have hh := support_empty_large S (emptySet S E inc ω) inc q (δ+u) hq hS (hZnonempty ω hω) hω.2
    simpa only [z,zx,pencil_inter_count] using hh
  have hea : ∀ ω∈G,((univ.filter (fun x => zx ω x<(4/5)*z ω/q)).card:ℝ)≤100*q^(n+3)/zmin := by
    intro ω hω
    have hh := PencilContrast.ambient_small_degree hdim (emptySet S E inc ω) (hZnonempty ω hω) hQ
    simp only [pencil_degree] at hh
    apply hh.trans
    exact div_le_div_of_nonneg_left (by positivity) hzmin hω.1
  have hh := row_success_probability μ S Ds Da (sample S) full typ zx z
    (fun x => (1-b x)^R) q tS tA (10*(δ+u)*(S.card:ℝ)) (100*q^(n+3)/zmin)
    (2*μmean) εs εa (Real.exp (-μmean/3))
    (Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)) G FS FA
    (fun x _ => (Set.to_countable _).measurableSet) (fun x => (Set.to_countable _).measurableSet)
    hq htS htA hgood hfs hfa (sample_size_tail S R (L*c))
    (fun ω hω => hzmin.trans_le hω.1) (fun ω _ x => Nat.cast_nonneg _)
    (fun x => (halpha x).2.2) herrors htypS hDa htypA hes hea
  exact hh

end
end SharpLogRamsey.PreparedRow

end

end OAI
