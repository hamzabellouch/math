import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedDescription
import OAI.Combinatorics.SharpRamsey.Learning.LearningScalar
import OAI.Combinatorics.SharpRamsey.Geometry.SparsePencilBounds

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation Real
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedShortRow_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPreparedShortRow_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedShortRow_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedShortRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma good_mono (S : Finset (Projectivization K V))
    (plane : B→Finset (Projectivization K V)) (bs : List (B×ℕ))
    {L cap cap' size size' : ℝ} {R : ℕ} {ω : Fin R×Projectivization K V→ℕ}
    (hc : cap'≤cap) (hs : size ≤ size') (h : good S plane bs L cap size ω) :
    good S plane bs L cap' size' ω := by
  obtain ⟨z,hz,hcap,hsize⟩ := h
  exact ⟨z,hz,hc.trans hcap,hsize.trans hs⟩

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma acceptProb_mono {Ω : Type*} [Fintype Ω] (p : PublicTables.Law Ω)
    (A A' : Ω→Prop) (h : ∀ x,A x→A' x) :
    PublicTables.acceptProb p A≤PublicTables.acceptProb p A' := by
  unfold PublicTables.acceptProb PublicTables.accepted
  apply sum_le_sum
  intro x _
  by_cases hx : A x
  · simp only [hx,h x hx,ite_true]
    exact le_rfl
  · simp only [hx,ite_false]
    split_ifs <;> simp [p.nonneg x]

theorem short_proposal
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (σ P B₀ C b e W : ℝ) (hσ : 1≤σ) (hqexp : exp σ=(Nat.card K:ℝ))
    (hP : 100000000000000≤P) (hPu : P≤σ) (hPL : P=(L:ℝ)*R)
    (hBdef : B₀=(Nat.card K:ℝ)^(n+2)/(S.card:ℝ))
    (hb : 0≤b) (he : 0≤e) (hloss : b+e≤P/1000000)
    (hpP : 10000*σ≤(p:ℝ)*P)
    (hDs : (Ds.card:ℝ)≤S.card*exp (-P/200)+(S.card:ℝ)/10000)
    (hDaSize : (Da.card:ℝ)≤2*S.card+S.card*exp (5*P))
    (hN : 2*(Nat.card K:ℝ)*P≤S.card)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤e)
    (hW : 0≤W) (hWb : W≤20804*(Nat.card K:ℝ)*B₀)
    (hWsum : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : (Nat.card K:ℝ)*B₀*exp (-b-e)/8≤(E₀.card:ℝ)*exp (-e)/2)
    (herror : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤((Nat.card K:ℝ)*B₀*exp (-b-e)/8)/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-e)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let z : ℝ := q*B₀*exp (-b-e)/8
  have hNpos : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hN1 : 1≤N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hq : 0<q := by rw [show q=exp σ from hqexp.symm]; exact exp_pos _
  have hBpos : 0<B₀ := by rw [hBdef]; positivity
  have hz : 0<z := by dsimp [z]; positivity
  have mean_eq : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hPL]
    dsimp [q]
    field_simp
  have htotal : (Fintype.card (Projectivization K V):ℝ)≤2*exp (3*σ) := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V (show Module.finrank K V=(n+2)+1 by omega)]
    push_cast
    have hq2 : 2≤q := by
      have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
      dsimp [q]
      exact_mod_cast hh
    apply (Incidence.geom_sum_le_twice_pow q hq2 (n+2)).trans
    have hh : q^(n+2)≤q^3 := pow_le_pow_right₀ (by linarith : 1≤q) (by omega)
    have heq : q^3=exp (3*σ) := by rw [show q=exp σ from hqexp.symm,←exp_nat_mul]; norm_num
    rw [←heq]
    linarith
  have hlow := LearningScalar.short_row_lower hσ hP hPu hBpos hN1
    (Nat.cast_nonneg (Fintype.card (Projectivization K V))) htotal hW
    (by simpa only [hqexp] using hWb) hb he hloss hpP
  simp only [hqexp] at hlow
  have hgeom := geometric_proposal_probability n R p h M hn hdim S₀ S U Ds Da hS hS₀ hSU hDa
    plane bs E E₀ hE₀ hE₀E c L hc hf B₀ C e (1/1000) (1/1000) z W (N/100) N
    (by norm_num) (by norm_num) hz (by positivity) hNpos hC hL hR hp hpe hB hQ hα
    hsmall hWsum hZ herror T a hs ha hM
  dsimp only at hgeom hlow
  rw [←hPL,mean_eq] at hgeom
  have hcap : N/2≤N-(Ds.card:ℝ)-N/100-(10*((1/1000:ℝ)+1/1000))*N :=
    LearningScalar.row_capture hNpos.le (by linarith) hDs
  have hsize : 2*(q*P)+(Da.card:ℝ)+N+100*q^(n+3)/z≤N*exp (6*P) := by
    dsimp [z]
    rw [hBdef]
    have hh := LearningScalar.row_size hNpos hq (by linarith : 100000≤P)
      (by linarith : b+e≤P) hN hDaSize (n+2)
    convert hh using 1; ring
  rw [show -P*(1/1000:ℝ)= -P/1000 by ring] at hgeom
  refine le_trans ?_ (le_trans hgeom ?_)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hlow
  · apply acceptProb_mono
    intro ω hω
    exact ⟨hω.1,hω.2.1,good_mono S plane (sized S₀ plane bs) hcap hsize hω.2.2⟩

end
end SharpLogRamsey.PreparedDescription

end

end OAI
