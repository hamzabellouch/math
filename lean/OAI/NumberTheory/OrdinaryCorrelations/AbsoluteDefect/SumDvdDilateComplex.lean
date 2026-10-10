import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CorePrime

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff

lemma sum_dvd_dilate_complex (u:ℕ) (hu:0<u) (X:ℝ) (hX:0≤X) (F:ℕ→ℂ) :
    (∑n∈(Finset.Icc 1 ⌊X⌋₊).filter (u∣·),F n)=∑v∈Icc 1 ⌊X/u⌋₊,F (u*v) := by
  have huR : (0:ℝ)<u := by exact_mod_cast hu
  have hXu : 0≤X/u := div_nonneg hX huR.le
  symm
  refine sum_bij (fun v _=>u*v) ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨hv1,hvN⟩:=Finset.mem_Icc.mp hv
    apply mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hu hv1,?_⟩,dvd_mul_right _ _⟩
    rw [Nat.le_floor_iff hX]
    have hvR:=(Nat.le_floor_iff hXu).mp hvN
    push_cast
    nlinarith [(le_div_iff₀ huR).mp hvR]
  · intro v hv w hw he;exact Nat.eq_of_mul_eq_mul_left hu he
  · intro n hn
    obtain ⟨hnI,v,rfl⟩:=mem_filter.mp hn
    refine ⟨v,?_,rfl⟩
    obtain ⟨hn1,hnN⟩:=Finset.mem_Icc.mp hnI
    refine Finset.mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hn1,?_⟩
    rw [Nat.le_floor_iff hXu,le_div_iff₀ huR]
    have hnR:=(Nat.le_floor_iff hX).mp hnN
    simpa [Nat.cast_mul,mul_comm] using hnR
  · intro v hv;rfl

noncomputable def choiceTerm (phi:ℝ→ℝ) (B:ℝ) (a f g:ℕ→ℂ) (h:ℕ) (X:ℝ)
    (q:Σ_:ℕ,Finset ℕ) : ℂ :=
  ∑x∈Icc 1 ⌊X⌋₊,a q.1*(divisorWeight B q.1:ℂ)*f x*g (x+h*q.1)*
    cut phi B q.1 x*cut phi B q.1 (x+h*q.1)*
    ((-1/4:ℂ)^q.2.card/(removed q.2:ℂ))*(if retained q.1 q.2∣x then 1 else 0)

lemma centered_eq_raw_add (phi:ℝ→ℝ) (B:ℝ) (D:Finset ℕ)
    (hD:∀d∈D,Squarefree d ∧ d≠0 ∧ d.primeFactors⊆core B∪center B)
    (a f g:ℕ→ℂ) (h:ℕ) (X:ℝ) :
    centeredSum phi B D a f g h X=rawSum phi B D a f g h X+
      ∑q∈choices B D,choiceTerm phi B a f g h X q := by
  classical
  have point (d:ℕ) (hd:d∈D) (x:ℕ) :
      a d*f x*g (x+h*d)*kernel phi B d x (x+h*d)=
      a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*cut phi B d x*cut phi B d (x+h*d)*
        (if d∣x then (1:ℂ) else 0)+
      ∑W∈(centralPrimes B d).powerset.erase ∅,
        a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*cut phi B d x*cut phi B d (x+h*d)*
          ((-1/4:ℂ)^W.card/(removed W:ℂ))*(if retained d W∣x then 1 else 0) := by
    rw [kernel_expansion phi B (hD d hd).1 (hD d hd).2.1 (hD d hd).2.2]
    let F (W:Finset ℕ) : ℂ := (-1/4:ℂ)^W.card/(removed W:ℂ)*
      (if retained d W∣x then 1 else 0)
    have hsum:=sum_erase_add (centralPrimes B d).powerset F (by simp : ∅∈(centralPrimes B d).powerset)
    have he0 : F ∅=(if d∣x then (1:ℂ) else 0) := by
      simp [F,removed,retained,Nat.prod_primeFactors_of_squarefree (hD d hd).1]
    change _*(_*(∑W∈(centralPrimes B d).powerset,F W))=_
    rw [←hsum,he0,mul_add,mul_add]
    simp only [mul_sum]
    have hterms : (∑W∈(centralPrimes B d).powerset.erase ∅,
        a d*f x*g (x+h*d)*(cut phi B d x*cut phi B d (x+h*d)*(divisorWeight B d:ℂ)*F W))=
      ∑W∈(centralPrimes B d).powerset.erase ∅,
        a d*(divisorWeight B d:ℂ)*f x*g (x+h*d)*cut phi B d x*cut phi B d (x+h*d)*
          ((-1/4:ℂ)^W.card/(removed W:ℂ))*(if retained d W∣x then 1 else 0) := by
      apply sum_congr rfl
      intro W hW
      dsimp [F]
      ring
    rw [hterms]
    ring
  unfold centeredSum rawSum
  simp_rw [sum_congr rfl (fun d hd=>point d hd _),sum_add_distrib]
  congr 1
  rw [Finset.sum_comm (s:=Icc 1 ⌊X⌋₊) (t:=D)]
  simp_rw [Finset.sum_comm (s:=Icc 1 ⌊X⌋₊)]
  exact sum_sigma' D (fun d=>(centralPrimes B d).powerset.erase ∅) _

lemma choiceTerm_dilate (phi:ℝ→ℝ) (B:ℝ) {d:ℕ} (hd:Squarefree d)
    (hd0:d≠0) (W:Finset ℕ) (hW:W⊆centralPrimes B d)
    (a f g:ℕ→ℂ) (h:ℕ) (X:ℝ) (hX:0≤X) :
    choiceTerm phi B a f g h X ⟨d,W⟩=
      (divisorWeight B (retained d W):ℂ)*
      ∑v∈Icc 1 ⌊X/(retained d W)⌋₊,
        ((a ((retained d W)*(removed W))*(-1/4:ℂ)^W.card)/(removed W:ℂ))*
        f (retained d W*v)*g (retained d W*(v+h*removed W))*
        cut phi B (retained d W) v*cut phi B (retained d W) (v+h*removed W) := by
  have hprod:=retained_mul_removed d hd W (hW.trans (centralPrimes_subset B hd0))
  have hx (v:ℕ) : retained d W*v+h*d=retained d W*(v+h*removed W) := by
    calc
      _ = retained d W*v+h*(retained d W*removed W) := by rw [hprod]
      _ = _ := by ring
  unfold choiceTerm
  change (∑x∈Icc 1 ⌊X⌋₊,_*(if retained d W∣x then (1:ℂ) else 0))=_
  simp_rw [mul_ite,mul_one,mul_zero]
  rw [←sum_filter,sum_dvd_dilate_complex _ (retained_pos d W) X hX]
  rw [mul_sum]
  apply sum_congr rfl
  intro v hv
  rw [hx,cut_dilation phi B hd0 W hW v,cut_dilation phi B hd0 W hW (v+h*removed W),
    retained_weight B hd0 W hW,hprod]
  ring
end OrdinaryAnalyticCentering

end

end OAI
