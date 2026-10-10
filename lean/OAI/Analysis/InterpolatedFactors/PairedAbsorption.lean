import OAI.Analysis.InterpolatedFactors.CornerIndex

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.PairedAbsorption
open RectangularAbsorption CircularRotation
variable {A : Type u_1} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {S : Type u_2} {P : Type u_3} [DecidableEq S] [DecidableEq P]
abbrev Index (S : Type u_4) (P : Type u_5) := PairedIndex S P

structure Input (B : StarSubalgebra ℂ A) (S : Type u_6) (P : Type u_7) [DecidableEq S] [DecidableEq P] where
  τ : B →ₗ[ℂ] ℂ
  tracial : ∀ a b,τ (a*b)=τ (b*a)
  p : Index S P → B
  q : Index S P → B
  projection : ∀ i,IsStarProjection (p i)
  projectionq : ∀ i,IsStarProjection (q i)
  pq : ∀ i,p (CircularRotation.flip i)=q i
  qp : ∀ i,q (CircularRotation.flip i)=p i
  raw : Index S P → ℕ → A
  extra : Index S P → A
  supported : ∀ i,(p i:A)*extra i*(q i:A)=extra i
  raw_cov : ∀ i j n m (a : B),star (raw i n)*(a:A)*raw j m=
    if i=j ∧ n=m then τ a • (1:A) else 0
  extra_cov : ∀ i j (a : B),star (extra i)*(a:A)*extra j=
    if i=j then τ (a*p i) • (q i:A) else 0
  raw_extra : ∀ i j n (a : B),star (raw i n)*(a:A)*extra j=0

namespace Input
variable {B : StarSubalgebra ℂ A} (d : Input B S P)

def reservoir (i : Index S P) (n : ℕ) : A := rotate (fun k => d.raw k n) i

theorem reservoir_cov (i j : Index S P) (n m : ℕ) (a : B) :
    star (d.reservoir i n)*(a:A)*d.reservoir j m=
      if i=j ∧ n=m then d.τ a • (1:A) else 0 := by
  by_cases hnm : n=m
  · subst m
    have hh := rotate_covariance (fun k => d.raw k n) (a:A) (d.τ a • (1:A))
      (fun i j => by simpa only [and_true] using d.raw_cov i j n n a) i j
    simpa only [reservoir,and_true] using hh
  · rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
    · simpa only [reservoir,rotate,hnm,and_false,ite_false] using d.raw_cov (.inl i) (.inl j) n m a
    · cases c <;> simp [reservoir,rotate,plus,minus,mul_add,mul_sub,d.raw_cov,hnm]
    · cases b <;> simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,d.raw_cov,hnm]
    · cases b <;> cases c <;>
        simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,mul_add,mul_sub,d.raw_cov,hnm]

theorem reservoir_extra (i j : Index S P) (n : ℕ) (a : B) :
    star (d.reservoir i n)*(a:A)*d.extra j=0 := by
  rcases i with i | ⟨i,b⟩
  · exact d.raw_extra (.inl i) j n a
  · cases b <;> simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,d.raw_extra]

def data (i : Index S P) : Data B where
  τ := d.τ
  tracial := d.tracial
  p := d.p i
  q := d.q i
  projection := d.projection i
  projectionq := d.projectionq i
  C := d.reservoir i
  D := d.extra i
  D_supported := d.supported i
  C_cov a n m := by simpa only [true_and] using d.reservoir_cov i i n m a
  D_cov a := by simpa only [ite_true] using d.extra_cov i i a
  C_D a n := d.reservoir_extra i i n a
  D_C a n := (Orthogonal.symm (d.reservoir_extra i i n)) a

def family : Family B (Index S P) where
  data := d.data
  CC i j hij n m a := by simpa only [data,hij,false_and,ite_false] using d.reservoir_cov i j n m a
  CD i j _ n a := d.reservoir_extra i j n a
  DD i j hij a := by simpa only [data,ite_eq_right hij] using d.extra_cov i j a

def output (i : Index S P) (n : ℕ) : A := d.family.output i n

theorem output_cov (i j : Index S P) (n m : ℕ) (a : B) :
    star (d.output i n)*(a:A)*d.output j m=
      if i=j ∧ n=m then d.τ a • (1:A) else 0 := by
  have hh := d.family.output_covariance i j n m a
  split_ifs with h
  · rw [ite_eq_left h] at hh; exact hh
  · rw [ite_eq_right h] at hh; exact hh

theorem output_generation (M : StarSubalgebra ℂ A)
    (hpM : ∀ i,(d.p i:A)∈M) (hqM : ∀ i,(d.q i:A)∈M) :
    ((∀ i,d.extra i+star (d.extra (CircularRotation.flip i))∈M) ∧
      ∀ i n,d.raw i n+star (d.raw i n)∈M) ↔
        ∀ i n,d.output i n+star (d.output (CircularRotation.flip i) n)∈M := by
  have hh := d.family.output_generation CircularRotation.flip d.pq d.qp M hpM hqM
  change ((∀ i,d.extra i+star (d.extra (CircularRotation.flip i))∈M) ∧
      ∀ i n,d.reservoir i n+star (d.reservoir (CircularRotation.flip i) n)∈M) ↔
      ∀ i n,d.output i n+star (d.output (CircularRotation.flip i) n)∈M at hh
  rw [← hh]
  apply and_congr_right
  intro _
  constructor
  · intro h i n
    exact (rotate_generation (fun k => d.raw k n) M).mp (fun k => h k n) i
  · intro h i n
    exact (rotate_generation (fun k => d.raw k n) M).mpr (fun k => h k n) i
end Input
end FreeGroupFactorMain.PairedAbsorption

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification RectangularAbsorption WeightedCornerIndex

abbrev Base (u v : ℝ) := pFilled u v (0:ℕ) 1

def kindCreator (u v : ℝ) : Kind → PCorner ℕ
  | .fresh n r s => pFresh u v 0 (n+2) r s
  | .residual r s => pResidual u v 0 1 r s
  | .diagonal r => pDiagonal u v 0 0 r

def kindLeft (u v : ℝ) : Kind → Base u v
  | .fresh _ r _ => pSupport u v 0 1 r
  | .residual r _ => pResidualSupport u v 0 1 r
  | .diagonal r => pSupport u v 0 1 r

def kindRight (u v : ℝ) : Kind → Base u v
  | .fresh _ _ s => pSupport u v 0 1 s
  | .residual _ s => pResidualSupport u v 0 1 s
  | .diagonal r => pSupport u v 0 1 r

theorem kindLeft_projection (u v : ℝ) (k : Kind) : IsStarProjection (kindLeft u v k) := by
  cases k
  · exact pSupport_projection u v 0 1 _
  · exact pResidualSupport_projection u v 0 1 _
  · exact pSupport_projection u v 0 1 _

theorem kindRight_projection (u v : ℝ) (k : Kind) : IsStarProjection (kindRight u v k) := by
  cases k
  · exact pSupport_projection u v 0 1 _
  · exact pResidualSupport_projection u v 0 1 _
  · exact pSupport_projection u v 0 1 _

theorem kindLeft_transpose (u v : ℝ) (k : Kind) : kindLeft u v k.transpose=kindRight u v k := by
  cases k <;> rfl

theorem kindRight_transpose (u v : ℝ) (k : Kind) : kindRight u v k.transpose=kindLeft u v k := by
  cases k <;> rfl

theorem kindCreator_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (k : Kind) :
    (kindLeft u v k : PCorner ℕ)*kindCreator u v k*(kindRight u v k : PCorner ℕ)=kindCreator u v k := by
  cases k
  · exact pFresh_supported u v hv hvu 0 1 _ _ _
  · exact pResidual_supported u v hv hvu 0 1 _ _
  · exact pDiagonal_supported u v hv hvu 0 1 0 _

theorem kindCreator_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (k l : Kind) (hk : k.valid) (hl : l.valid) (a : Base u v) :
    star (kindCreator u v k)*(a : PCorner ℕ)*kindCreator u v l=
      if k=l then pTrace u v 0 1 (a*kindLeft u v k) • (kindRight u v k : PCorner ℕ) else 0 := by
  cases k with
  | fresh n r s =>
    cases l with
    | fresh m t w =>
      have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (n+2) (m+2) (by omega)
        (by omega) (by omega) (by omega) (by omega) r s t w a
      simpa only [kindCreator,kindLeft,kindRight,Kind.fresh.injEq,Nat.add_right_cancel_iff] using hh
    | residual t w =>
      rw [ite_eq_right (by simp)]
      exact pFresh_residual u v (0:ℕ) 1 (n+2) (by omega) (by omega) (by omega) r s t w hl a
    | diagonal t =>
      rw [ite_eq_right (by simp)]
      exact pFresh_diagonal u v (0:ℕ) 1 (n+2) 0 (by omega) (by omega) (by omega) (by omega) (by omega) r s t a
  | residual r s =>
    cases l with
    | fresh m t w =>
      rw [ite_eq_right (by simp)]
      exact (pFresh_residual u v (0:ℕ) 1 (m+2) (by omega) (by omega) (by omega) t w r s hk).symm a
    | residual t w =>
      simpa only [kindCreator,kindLeft,kindRight,Kind.residual.injEq]
        using pResidual_covariance u v hu hv (0:ℕ) 1 (by omega) r s t w hk hl a
    | diagonal t =>
      rw [ite_eq_right (by simp)]
      exact pResidual_diagonal u v (0:ℕ) 1 0 (by omega) (by omega) r s hk t a
  | diagonal r =>
    cases l with
    | fresh m t w =>
      rw [ite_eq_right (by simp)]
      exact (pFresh_diagonal u v (0:ℕ) 1 (m+2) 0 (by omega) (by omega) (by omega) (by omega) (by omega) t w r).symm a
    | residual t w =>
      rw [ite_eq_right (by simp)]
      exact (pResidual_diagonal u v (0:ℕ) 1 0 (by omega) (by omega) t w hl r).symm a
    | diagonal t =>
      simpa only [kindCreator,kindLeft,kindRight,Kind.diagonal.injEq,true_and]
        using pDiagonal_covariance u v hu hv (0:ℕ) 1 0 0 (by omega) (by omega) (by omega) r t a

def rawReservoir (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) : PCorner ℕ :=
  pFresh u v 0 (reservoirCode (i,n)+2) false false

theorem rawReservoir_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : WeightedCornerIndex.Index) (n m : ℕ) (a : Base u v) :
    star (rawReservoir u v i n)*(a : PCorner ℕ)*rawReservoir u v j m=
      if i=j ∧ n=m then pTrace u v 0 1 a • (1:PCorner ℕ) else 0 := by
  have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (reservoirCode (i,n)+2) (reservoirCode (j,m)+2)
    (by omega) (by omega) (by omega) (by omega) (by omega) false false false false a
  simpa only [rawReservoir,and_true,pSupport_false,mul_one,OneMemClass.coe_one,
    Nat.add_right_cancel_iff,reservoirCode.injective.eq_iff,Prod.mk.injEq] using hh

theorem rawReservoir_extra (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : WeightedCornerIndex.Index) (n : ℕ) (k : Kind) (hk : k.valid) (a : Base u v) :
    star (rawReservoir u v i n)*(a : PCorner ℕ)*kindCreator u v k=0 := by
  cases k with
  | fresh m r s =>
    have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (reservoirCode (i,n)+2) (m+2)
      (by omega) (by omega) (by omega) (by omega) (by omega) false false r s a
    rw [ite_eq_right (fun h => hk ⟨h.2.1.symm,h.2.2.symm⟩)] at hh
    exact hh
  | residual r s =>
    exact pFresh_residual u v (0:ℕ) 1 (reservoirCode (i,n)+2)
      (by omega) (by omega) (by omega) false false r s hk a
  | diagonal r =>
    exact pFresh_diagonal u v (0:ℕ) 1 (reservoirCode (i,n)+2) 0
      (by omega) (by omega) (by omega) (by omega) (by omega) false false r a

def cornerAbsorption (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    PairedAbsorption.Input (Base u v) SelfIndex PairIndex where
  τ := pTrace u v 0 1
  tracial := pTrace_tracial u v (hv.trans hvu).ne' hv.ne' 0 1
  p i := kindLeft u v (description i)
  q i := kindRight u v (description i)
  projection i := kindLeft_projection u v _
  projectionq i := kindRight_projection u v _
  pq i := by rw [description_flip,kindLeft_transpose]
  qp i := by rw [description_flip,kindRight_transpose]
  raw := rawReservoir u v
  extra i := kindCreator u v (description i)
  supported i := kindCreator_supported u v hv hvu _
  raw_cov := rawReservoir_covariance u v (hv.trans hvu).ne' hv.ne'
  extra_cov i j a := by
    simpa only [description_injective.eq_iff] using
      kindCreator_covariance u v (hv.trans hvu).ne' hv.ne' _ _ (description_valid i) (description_valid j) a
  raw_extra i j n a := rawReservoir_extra u v (hv.trans hvu).ne' hv.ne' i n _ (description_valid j) a
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.PairedAbsorption.Input
open RectangularAbsorption CircularRotation
variable {A : Type u_8} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {S : Type u_9} {P : Type u_10} [DecidableEq S] [DecidableEq P]
variable {B : StarSubalgebra ℂ A} (d : PairedAbsorption.Input B S P)

theorem output_mem (K : Submodule ℂ A)
    (hK : ∀ p q : B, ∀ x∈K,(p:A)*x*(q:A)∈K)
    (hextra : ∀ i,d.extra i∈K) (hraw : ∀ i n,d.raw i n∈K) (i : Index S P) (n : ℕ) :
    d.output i n∈K := by
  have hr (i : Index S P) (n : ℕ) : d.reservoir i n∈K := by
    rcases i with i | ⟨i,b⟩
    · exact hraw _ n
    · cases b
      · exact K.add_mem (K.smul_mem _ (hraw _ n)) (K.smul_mem _ (hraw _ n))
      · exact K.sub_mem (K.smul_mem _ (hraw _ n)) (K.smul_mem _ (hraw _ n))
  have hp (n : ℕ) : part (d.p i:A) (d.q i:A) (d.reservoir i) n∈K := hK _ _ _ (hr i n)
  have hrem (n : ℕ) : remainder (d.p i:A) (d.q i:A) (d.reservoir i) n∈K := K.sub_mem (hr i n) (hp n)
  cases n with
  | zero => exact K.add_mem (hextra i) (hrem 0)
  | succ n => exact K.add_mem (hp n) (hrem (n+1))
end FreeGroupFactorMain.PairedAbsorption.Input

end

end OAI
