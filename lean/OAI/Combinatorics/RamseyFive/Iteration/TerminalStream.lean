import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.CompressionStage
import OAI.Combinatorics.RamseyFive.Entropy.FinalMarking

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
local instance tsFinDE (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem eventually_no_terminal_stream {η : ℝ} (hη : 0<η) (c d : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K V α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ : ℝ)
      (_S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M),
      finrank K V=5→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      Λ≤k₀→0≤Δ→Δ≤c/9600*σ^η→False := by
  filter_upwards [eventually_stream_entropy_gain hη c d (2+1/c+Real.log 800) hc] with σ hent
  intro K V α _ _ _ _ _ _ _ _ _ _ _ _ _ N n adm Λ Δ M k₀ S
    hd hσ hq hα hN hlen hk hΛ hΔ hΔhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hn : 0<(n:ℝ) := (by positivity : 0<c*(Nat.card K:ℝ)*σ^(1+η)).trans_le hlen
  have hlow:=hent S.sample α (FlagPair K V) N n adm S.stream hσ hα hN
    (by simpa only [hq] using hlen) S.density_bound
  have hfin:=S.final_entropy_bound hd hΔ
  have hE:=expensiveBound_coarse (K:=K) (V:=V) hd σ hσ hq
  rw [hq] at hE
  have hEC : expensiveBound K V*Δ≤(n:ℝ) := by
    calc
      _ ≤ (9600*(Nat.card K:ℝ)*σ)*(c/9600*σ^η) :=
        mul_le_mul hE hΔhi hΔ (by positivity)
      _ = c*(Nat.card K:ℝ)*σ^(1+η) := by rw [Real.rpow_add hs,Real.rpow_one];ring
      _ ≤ n := hlen
  have hΛhi : Λ≤(n:ℝ)/c := by
    apply hΛ.trans
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=4*σ+Real.log 153 := by
    rw [Real.log_mul (by norm_num) (pow_pos hp _).ne',Real.log_pow,←hq,Real.log_exp]
    norm_num;ring
  conv_rhs at hfin => rw [hJ]
  have hdiv : (n:ℝ)/c=(n:ℝ)*(1/c) := by ring
  rw [hdiv] at hΛhi
  have hlow' : (n:ℝ)*(4*σ+Real.log 153+(2+1/c+Real.log 800))≤entropy (map S.stream.law S.stream.tuple) := by
    convert hlow using 1; congr 1; exact Subsingleton.elim _ _
  nlinarith only [hlow',hfin,hEC,hΛhi,hn]
end

noncomputable section
variable (K α : Type) [Field K] [Finite K] [Fintype α]

structure PolarState (N n : ℕ) (adm : (Fin N→α)→Prop) (d Λ Δ M : ℝ) where
  ambient : Type
  [group : AddCommGroup ambient]
  [module : Module K ambient]
  [dimension : FiniteDimensional K ambient]
  [points : Fintype (ℙ K ambient)]
  [hyperplanes : Fintype (ℙ K (Dual K ambient))]
  [bipoints : Fintype (ℙ K (Dual K (Dual K ambient)))]
  [pointNonempty : Nonempty (ℙ K ambient)]
  [planeNonempty : Nonempty (ℙ K (Dual K ambient))]
  [bipointNonempty : Nonempty (ℙ K (Dual K (Dual K ambient)))]
  dim : finrank K ambient=5
  coded : CodedStream (K:=K) (V:=ambient) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M
attribute [instance] PolarState.group PolarState.module PolarState.dimension PolarState.points
  PolarState.hyperplanes PolarState.bipoints PolarState.pointNonempty PolarState.planeNonempty
  PolarState.bipointNonempty
variable {K α}
def PolarState.of {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype (ℙ K (Dual K (Dual K V)))]
    [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
    {N n : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M : ℝ} (hd : finrank K V=5)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M) :
    PolarState K α N n adm d Λ Δ M where
  ambient:=V
  dim:=hd
  coded:=S

theorem eventually_polar_compression {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0<c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ D : ℝ)
      (_S : PolarState K α N n adm d Λ Δ M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤Λ→0≤Δ→0≤M→M≤Cm*σ→
      D=σ^beta η*(1+Λ/k₀+Δ*σ^(-η))→σ^beta η≤D→D≤σ^(1-η/2)→
      Nonempty (PolarState K α N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_actual_compression hη hη' c d Cm hc hCm] with σ h
  intro q₀ K α _ _ _ _ _ N n adm Λ Δ M k₀ D S hq3 hcard hσ hq hα hN hlen hn hk hklo
    hΛ hΔ hM hMhi hDeq hD hDhi
  have hh:=h q₀ K S.ambient α N n adm Λ Δ M k₀ D S.coded S.dim hq3 hcard hσ hq hα hN
    hlen hn hk hklo hΛ hΔ hM hMhi hDeq hD hDhi
  rcases hh with h|h
  · obtain ⟨T⟩:=h
    exact ⟨PolarState.of S.dim T⟩
  · obtain ⟨T⟩:=h
    let : Fintype (ℙ K (Dual K (Dual K (Dual K S.ambient)))):=
      Fintype.ofEquiv (ℙ K (Dual K S.ambient)) bidualPoint
    let : Nonempty (ℙ K (Dual K (Dual K (Dual K S.ambient)))) :=
      ⟨bidualPoint (Classical.arbitrary (ℙ K (Dual K S.ambient)))⟩
    exact ⟨PolarState.of (by simpa using S.dim) T⟩

theorem eventually_polar_terminal {η : ℝ} (hη : 0<η) (c d : ℝ) (hc : 0<c) :
    ∀ᶠ σ : ℝ in atTop,∀ (K α : Type) [Field K] [Finite K] [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ : ℝ)
      (_S : PolarState K α N n adm d Λ Δ M),
      1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      Λ≤k₀→0≤Δ→Δ≤c/9600*σ^η→False := by
  filter_upwards [eventually_no_terminal_stream hη c d hc] with σ h
  intro K α _ _ _ _ N n adm Λ Δ M k₀ S hσ hq hα hN hlen hk hΛ hΔ hΔhi
  exact h K S.ambient α N n adm Λ Δ M k₀ S.coded S.dim hσ hq hα hN hlen hk hΛ hΔ hΔhi
end
end

open FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]

lemma iid_uniform_mass (N : ℕ) (s : Fin N→α) :
    iid (uniform Fintype.card_pos) (Fin N) s=1/(Fintype.card α:ℝ)^N := by
  simp [iid,uniform]

def initialSelectedStream {N n : ℕ} (admissible : (Fin N→α)→Prop)
    (E : Finset (Fin N→α))
    (hE : 0<eventMass (iid (uniform Fintype.card_pos) (Fin N)) E)
    (hgood : ∀ s,s∈E→admissible s)
    (choose : (Fin N→α)→(Fin n↪o Fin N))
    (decode : α→β) (encode : β→α) (hinv : Function.LeftInverse encode decode) :
    SelectedStream (Ω:=Fin N→α) (β:=β) N n admissible where
  law := conditionOn (iid (uniform Fintype.card_pos) (Fin N)) E hE
  stream := id
  tuple := fun s i=>decode (s (choose s i))
  reverse := false
  view := encode
  selected := by
    intro s hs
    apply (mem_occurrences_iff _ _).mpr
    refine ⟨choose s,fun i=>?_⟩
    exact (hinv _).symm
  good := fun s hs=>hgood s (conditionOn_positive _ E hE s hs).1
  density := 1/eventMass (iid (uniform Fintype.card_pos) (Fin N)) E
  density_nonneg := by positivity
  density_bound := by
    intro s
    rw [map_id]
    have h:=conditionOn_le (iid (uniform Fintype.card_pos) (Fin N)) E hE s
    rw [iid_uniform_mass] at h
    convert h using 1; ring

def firstWitness {N n : ℕ} (hn : n≤N) (P : (Fin N→α)→(Fin n↪o Fin N)→Prop)
    (s : Fin N→α) : Fin n↪o Fin N :=
  if h : ∃ e,P s e then h.choose else
    { toFun := fun i=>⟨i.val,lt_of_lt_of_le i.isLt hn⟩
      inj' := by intro i j h; exact Fin.ext (congrArg (fun x : Fin N=>x.val) h)
      map_rel_iff' := by intro i j; rfl }

omit [Fintype α] [Nonempty α] in
lemma firstWitness_spec {N n : ℕ} (hn : n≤N)
    (P : (Fin N→α)→(Fin n↪o Fin N)→Prop) (s : Fin N→α)
    (h : ∃ e,P s e) : P s (firstWitness hn P s) := by
  simp only [firstWitness,dite_eq_left h]
  exact h.choose_spec

omit [Fintype β] in
theorem initial_selected_exists {N n : ℕ} (hn : n≤N)
    (admissible : (Fin N→α)→Prop) (consistent : (Fin n→β)→Prop)
    (E : Finset (Fin N→α))
    (hE : 0<eventMass (iid (uniform Fintype.card_pos) (Fin N)) E)
    (hgood : ∀ s,s∈E→admissible s)
    (decode : α→β) (encode : β→α) (hinv : Function.LeftInverse encode decode)
    (hselect : ∀ s,s∈E→∃ e : Fin n↪o Fin N,consistent (fun i=>decode (s (e i)))) :
    ∃ S : SelectedStream (Ω:=Fin N→α) (β:=β) N n admissible,
      S.density=1/eventMass (iid (uniform Fintype.card_pos) (Fin N)) E ∧
      (∀ s,0<S.law s→consistent (S.tuple s)) := by
  let P:=fun (s : Fin N→α) (e : Fin n↪o Fin N)=>consistent (fun i=>decode (s (e i)))
  let S:=initialSelectedStream admissible E hE hgood (firstWitness hn P) decode encode hinv
  refine ⟨S,rfl,?_⟩
  intro s hs
  exact firstWitness_spec hn P s (hselect s (conditionOn_positive _ E hE s hs).1)

end

end SharpRamseyFive.SelectedTuple

end OAI
