import OAI.NumberTheory.TotientAsymptotic.FixedCoordinateValueStrip
import OAI.NumberTheory.TotientAsymptotic.TerminalSliceCount

namespace OAI

/-! Sum the fixed-coordinate strip estimate over the actual floor partition
of the terminal coordinate. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

/-- Distinct values with one fixed bad coordinate retain the exponential
saving after all terminal-coordinate strips have been summed. -/
theorem ppt_fixed_coordinate_value_count (H : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, N+3+H=m x → ∀ i : Fin (N+2), P ≤ m x-(i.val+1) →
      ∀ Q : Finset ℕ, ∀ n : ℕ→ℕ,
      (∀ v∈Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        N+3 ≤ (n v).primeFactorsList.length ∧
        fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
        2 < fordPrimeCoordinate (n v) (N+3) ∧
        ∀ j < N+3, fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤
          xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
      (∀ v∈Q, primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1)) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*
        Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
  classical
  obtain ⟨A,a,c,hA,ha,hc,hcount⟩ := fixed_coordinate_value_strip H
  let T := ∑' k : ℕ, terminalMassWeight a k
  have hT : 0 ≤ T := tsum_nonneg (fun k => (terminalMassWeight_pos a k).le)
  refine ⟨A*(T+1),c,by positivity,hc,?_⟩
  filter_upwards [hcount] with P hP
  filter_upwards [hP,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm i hi Q n hQ hbad
  let key : ℕ→ℕ := fun v => ⌊fordPrimeCoordinate (n v) (N+3)⌋₊
  let I := Q.image key
  let R (k : ℕ) := Q.filter (fun v => key v=k)
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨key v,Finset.mem_image.mpr ⟨v,hv,rfl⟩,
      Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ k∈I,((R k).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  let E := Real.exp (-c*(N+2-(i.val+1):ℕ))
  have hrow (k : ℕ) (hk : k∈I) : ((R k).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*E := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
    have hk2 : 2 ≤ key v := Nat.le_floor (hQ v hv).2.2.2.2.2.2.1.le
    apply hx N hNm i hi (key v) hk2 (R (key v)) n
    · intro w hw
      have hwQ := (Finset.mem_filter.mp hw).1
      obtain ⟨hn,hphi,hhead,hwx,hlen,hgap,_hlarge,hrows⟩ := hQ w hwQ
      exact ⟨hn,hphi,hhead,hwx,hlen,hgap,hrows⟩
    · intro w hw
      obtain ⟨hwQ,hkey⟩ := Finset.mem_filter.mp hw
      constructor
      · rw [←hkey]
        exact Nat.floor_le (le_max_left _ _)
      · rw [←hkey]
        exact (Nat.lt_floor_add_one _).le
    · intro w hw
      exact hbad w (Finset.mem_filter.mp hw).1
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+2)*E := by
    have hlog := Real.log_pos hx1
    have hG := G_pos hB (N+2)
    have hE : 0 < E := Real.exp_pos _
    positivity
  calc
    _ ≤ ∑ k∈I,((R k).card:ℝ) := hcard
    _ ≤ ∑ k∈I,A*(x/Real.log x)*G x (N+2)*terminalMassWeight a k*E :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+2)*E)*(∑ k∈I,terminalMassWeight a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (A*(x/Real.log x)*G x (N+2)*E)*T :=
      mul_le_mul_of_nonneg_left (finite_terminal_mass_bound ha I) hfac
    _ ≤ (A*(x/Real.log x)*G x (N+2)*E)*(T+1) :=
      mul_le_mul_of_nonneg_left (by linarith) hfac
    _ = _ := by dsimp only [E]; ring

/-- Sum the reversed-coordinate exponential weights, retaining the exact
fixed terminal loss in the constant. -/
lemma ppt_fixed_coordinate_exponential_sum {N H P m : ℕ} {c : ℝ}
    (hc : 0 < c) (hm : N+3+H=m) (hP : H+1 ≤ P)
    (I : Finset (Fin (N+2))) (hI : ∀ i∈I,P ≤ m-(i.val+1)) :
    (∑ i∈I,Real.exp (-c*(N+2-(i.val+1):ℕ))) ≤
      (Real.exp (c*(H+1:ℕ))/ (1-Real.exp (-c)))*Real.exp (-c*(P:ℝ)) := by
  classical
  let K := P-(H+1)
  let f : Fin (N+2)→ℕ := fun i => N+2-(i.val+1)
  have hinj : Set.InjOn f (I : Set (Fin (N+2))) := by
    intro i _ j _ hij
    apply Fin.ext
    have hi:=i.isLt
    have hj:=j.isLt
    dsimp only [f] at hij
    omega
  have hsub : I.image f ⊆ Finset.Ico K (N+2) := by
    intro r hr
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hr
    have hh:=hI i hi
    have hil:=i.isLt
    dsimp only [K,f]
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  have hrewrite (r : ℕ) : Real.exp (-c*(r:ℝ))=Real.exp (-c)^r := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  have hbound : (∑ i∈I,Real.exp (-c*(f i:ℝ))) ≤
      Real.exp (-c*(K:ℝ))/(1-Real.exp (-c)) := by
    calc
      _ = ∑ r∈I.image f,Real.exp (-c*(r:ℝ)) := (Finset.sum_image hinj).symm
      _ ≤ ∑ r∈Finset.Ico K (N+2),Real.exp (-c*(r:ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>(Real.exp_pos _).le)
      _ = ∑ r∈Finset.Ico K (N+2),Real.exp (-c)^r := by simp_rw [hrewrite]
      _ ≤ Real.exp (-c)^K/(1-Real.exp (-c)) :=
        geom_sum_Ico_le_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (by linarith only [hc]))
      _ = _ := by rw [←hrewrite]
  apply hbound.trans_eq
  have hK : (K:ℝ)=(P:ℝ)-(H+1:ℕ) := by
    dsimp only [K]
    exact Nat.cast_sub hP
  rw [hK]
  have he : -c*((P:ℝ)-(H+1:ℕ))=c*(H+1:ℕ)+(-c*(P:ℝ)) := by ring
  rw [he,Real.exp_add]
  ring

/-- A finite family with some bad retained coordinate has exponentially
small cardinality, uniformly after the fixed terminal cutoff. -/
theorem ppt_fixed_bad_coordinate_value_count (H : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ, N+3+H=m x → ∀ Q : Finset ℕ, ∀ n : ℕ→ℕ,
      (∀ v∈Q, 0 < n v ∧ (n v).totient=v ∧
        x^(1/4:ℝ) ≤ fordPrime (n v) 0 ∧ (v:ℝ) ≤ x ∧
        N+3 ≤ (n v).primeFactorsList.length ∧
        fordPrime (n v) (N+3) < fordPrime (n v) (N+2) ∧
        2 < fordPrimeCoordinate (n v) (N+3) ∧
        ∀ j < N+3,fordRowSum (N+3) (fordPrimeCoordinate (n v)) j ≤
          xi x j*(if j=0 then B x else fordPrimeCoordinate (n v) j)) →
      (∀ v∈Q,∃ j∈Finset.Icc 1 (m x-P),
        primeDoubleLog (n v) j < (19/20:ℝ)*fordBandScale x j ∨
          (21/20:ℝ)*fordBandScale x j < primeDoubleLog (n v) j) →
      (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (N+2)*Real.exp (-c*(P:ℝ)) := by
  classical
  obtain ⟨A,c,hA,hc,hcount⟩:=ppt_fixed_coordinate_value_count H
  let D:=Real.exp (c*(H+1:ℕ))/(1-Real.exp (-c))
  have hD : 0 < D := by
    have hh : Real.exp (-c) < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hc])
    exact div_pos (Real.exp_pos _) (sub_pos.mpr hh)
  refine ⟨A*D,c,mul_pos hA hD,hc,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (H+1)] with P hP hPH
  filter_upwards [hP,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hx1 hB
  intro N hNm Q n hQ hbad
  let I := Finset.univ.filter (fun i : Fin (N+2) => P ≤ m x-(i.val+1))
  let R (i : Fin (N+2)) := Q.filter (fun v =>
    primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
      (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1))
  have hcover : Q ⊆ I.biUnion R := by
    intro v hv
    obtain ⟨j,hj,hbj⟩:=hbad v hv
    have hj':=Finset.mem_Icc.mp hj
    let i : Fin (N+2):=⟨j-1,by omega⟩
    have hij : i.val+1=j := by dsimp only [i]; omega
    have hi : P ≤ m x-(i.val+1) := by rw [hij]; omega
    have hbi : primeDoubleLog (n v) (i.val+1) < (19/20:ℝ)*fordBandScale x (i.val+1) ∨
        (21/20:ℝ)*fordBandScale x (i.val+1) < primeDoubleLog (n v) (i.val+1) := by
      simpa only [hij] using hbj
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,
      Finset.mem_filter.mpr ⟨hv,hbi⟩⟩
  have hcard : (Q.card:ℝ) ≤ ∑ i∈I,((R i).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrow (i) (hi : i∈I) : ((R i).card:ℝ) ≤
      A*(x/Real.log x)*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) := by
    apply hx N hNm i (Finset.mem_filter.mp hi).2 (R i) n
    · intro v hv
      exact hQ v (Finset.mem_filter.mp hv).1
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
  have hfac : 0 ≤ A*(x/Real.log x)*G x (N+2) := by
    have hlog:=Real.log_pos hx1
    have hG:=G_pos hB (N+2)
    positivity
  calc
    _ ≤ ∑ i∈I,((R i).card:ℝ) := hcard
    _ ≤ ∑ i∈I,A*(x/Real.log x)*G x (N+2)*Real.exp (-c*(N+2-(i.val+1):ℕ)) :=
      Finset.sum_le_sum hrow
    _ = (A*(x/Real.log x)*G x (N+2))*(∑ i∈I,Real.exp (-c*(N+2-(i.val+1):ℕ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (A*(x/Real.log x)*G x (N+2))*(D*Real.exp (-c*(P:ℝ))) :=
      mul_le_mul_of_nonneg_left (ppt_fixed_coordinate_exponential_sum hc hNm hPH I
        (fun i hi=>(Finset.mem_filter.mp hi).2)) hfac
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
