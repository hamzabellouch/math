import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData30
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionData31
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData29

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedMerge960 : Integer.Sparse Master := [(Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000)]

def originalMerge960 : Integer.Sparse OriginalKey := originalTerm962 ++ originalTerm963

theorem reducedMerge960Check : reducedMerge960 = Integer.Sparse.mergeBy masterLess reducedTerm962 reducedTerm963 := by decide +kernel

def reducedMerge961 : Integer.Sparse Master := [(Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def originalMerge961 : Integer.Sparse OriginalKey := originalTerm964 ++ originalTerm965

theorem reducedMerge961Check : reducedMerge961 = Integer.Sparse.mergeBy masterLess reducedTerm964 reducedTerm965 := by decide +kernel

def reducedMerge962 : Integer.Sparse Master := [(Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def originalMerge962 : Integer.Sparse OriginalKey := originalMerge960 ++ originalMerge961

theorem reducedMerge962Check : reducedMerge962 = Integer.Sparse.mergeBy masterLess reducedMerge960 reducedMerge961 := by decide +kernel

def reducedMerge963 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000)]

def originalMerge963 : Integer.Sparse OriginalKey := originalMerge959 ++ originalMerge962

theorem reducedMerge963Check : reducedMerge963 = Integer.Sparse.mergeBy masterLess reducedMerge959 reducedMerge962 := by decide +kernel

def reducedMerge964 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000)]

def originalMerge964 : Integer.Sparse OriginalKey := originalTerm966 ++ originalTerm967

theorem reducedMerge964Check : reducedMerge964 = Integer.Sparse.mergeBy masterLess reducedTerm966 reducedTerm967 := by decide +kernel

def reducedMerge965 : Integer.Sparse Master := [(Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000)]

def originalMerge965 : Integer.Sparse OriginalKey := originalTerm968 ++ originalTerm969

theorem reducedMerge965Check : reducedMerge965 = Integer.Sparse.mergeBy masterLess reducedTerm968 reducedTerm969 := by decide +kernel

def reducedMerge966 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000)]

def originalMerge966 : Integer.Sparse OriginalKey := originalMerge964 ++ originalMerge965

theorem reducedMerge966Check : reducedMerge966 = Integer.Sparse.mergeBy masterLess reducedMerge964 reducedMerge965 := by decide +kernel

def reducedMerge967 : Integer.Sparse Master := [(Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000)]

def originalMerge967 : Integer.Sparse OriginalKey := originalTerm970 ++ originalTerm971

theorem reducedMerge967Check : reducedMerge967 = Integer.Sparse.mergeBy masterLess reducedTerm970 reducedTerm971 := by decide +kernel

def reducedMerge968 : Integer.Sparse Master := [(Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def originalMerge968 : Integer.Sparse OriginalKey := originalTerm972 ++ originalTerm973

theorem reducedMerge968Check : reducedMerge968 = Integer.Sparse.mergeBy masterLess reducedTerm972 reducedTerm973 := by decide +kernel

def reducedMerge969 : Integer.Sparse Master := [(Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def originalMerge969 : Integer.Sparse OriginalKey := originalMerge967 ++ originalMerge968

theorem reducedMerge969Check : reducedMerge969 = Integer.Sparse.mergeBy masterLess reducedMerge967 reducedMerge968 := by decide +kernel

def reducedMerge970 : Integer.Sparse Master := [(Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def originalMerge970 : Integer.Sparse OriginalKey := originalMerge966 ++ originalMerge969

theorem reducedMerge970Check : reducedMerge970 = Integer.Sparse.mergeBy masterLess reducedMerge966 reducedMerge969 := by decide +kernel

def reducedMerge971 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000)]

def originalMerge971 : Integer.Sparse OriginalKey := originalMerge963 ++ originalMerge970

theorem reducedMerge971Check : reducedMerge971 = Integer.Sparse.mergeBy masterLess reducedMerge963 reducedMerge970 := by decide +kernel

def reducedMerge972 : Integer.Sparse Master := [(Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000)]

def originalMerge972 : Integer.Sparse OriginalKey := originalTerm975 ++ originalTerm976

theorem reducedMerge972Check : reducedMerge972 = Integer.Sparse.mergeBy masterLess reducedTerm975 reducedTerm976 := by decide +kernel

def reducedMerge973 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000)]

def originalMerge973 : Integer.Sparse OriginalKey := originalTerm974 ++ originalMerge972

theorem reducedMerge973Check : reducedMerge973 = Integer.Sparse.mergeBy masterLess reducedTerm974 reducedMerge972 := by decide +kernel

def reducedMerge974 : Integer.Sparse Master := [(Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000)]

def originalMerge974 : Integer.Sparse OriginalKey := originalTerm977 ++ originalTerm978

theorem reducedMerge974Check : reducedMerge974 = Integer.Sparse.mergeBy masterLess reducedTerm977 reducedTerm978 := by decide +kernel

def reducedMerge975 : Integer.Sparse Master := [(Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def originalMerge975 : Integer.Sparse OriginalKey := originalTerm979 ++ originalTerm980

theorem reducedMerge975Check : reducedMerge975 = Integer.Sparse.mergeBy masterLess reducedTerm979 reducedTerm980 := by decide +kernel

def reducedMerge976 : Integer.Sparse Master := [(Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def originalMerge976 : Integer.Sparse OriginalKey := originalMerge974 ++ originalMerge975

theorem reducedMerge976Check : reducedMerge976 = Integer.Sparse.mergeBy masterLess reducedMerge974 reducedMerge975 := by decide +kernel

def reducedMerge977 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000)]

def originalMerge977 : Integer.Sparse OriginalKey := originalMerge973 ++ originalMerge976

theorem reducedMerge977Check : reducedMerge977 = Integer.Sparse.mergeBy masterLess reducedMerge973 reducedMerge976 := by decide +kernel

def reducedMerge978 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000)]

def originalMerge978 : Integer.Sparse OriginalKey := originalTerm981 ++ originalTerm982

theorem reducedMerge978Check : reducedMerge978 = Integer.Sparse.mergeBy masterLess reducedTerm981 reducedTerm982 := by decide +kernel

def reducedMerge979 : Integer.Sparse Master := [(Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000)]

def originalMerge979 : Integer.Sparse OriginalKey := originalTerm983 ++ originalTerm984

theorem reducedMerge979Check : reducedMerge979 = Integer.Sparse.mergeBy masterLess reducedTerm983 reducedTerm984 := by decide +kernel

def reducedMerge980 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000)]

def originalMerge980 : Integer.Sparse OriginalKey := originalMerge978 ++ originalMerge979

theorem reducedMerge980Check : reducedMerge980 = Integer.Sparse.mergeBy masterLess reducedMerge978 reducedMerge979 := by decide +kernel

def reducedMerge981 : Integer.Sparse Master := [(Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000)]

def originalMerge981 : Integer.Sparse OriginalKey := originalTerm985 ++ originalTerm986

theorem reducedMerge981Check : reducedMerge981 = Integer.Sparse.mergeBy masterLess reducedTerm985 reducedTerm986 := by decide +kernel

def reducedMerge982 : Integer.Sparse Master := [(Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def originalMerge982 : Integer.Sparse OriginalKey := originalTerm987 ++ originalTerm988

theorem reducedMerge982Check : reducedMerge982 = Integer.Sparse.mergeBy masterLess reducedTerm987 reducedTerm988 := by decide +kernel

def reducedMerge983 : Integer.Sparse Master := [(Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def originalMerge983 : Integer.Sparse OriginalKey := originalMerge981 ++ originalMerge982

theorem reducedMerge983Check : reducedMerge983 = Integer.Sparse.mergeBy masterLess reducedMerge981 reducedMerge982 := by decide +kernel

def reducedMerge984 : Integer.Sparse Master := [(Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def originalMerge984 : Integer.Sparse OriginalKey := originalMerge980 ++ originalMerge983

theorem reducedMerge984Check : reducedMerge984 = Integer.Sparse.mergeBy masterLess reducedMerge980 reducedMerge983 := by decide +kernel

def reducedMerge985 : Integer.Sparse Master := [(Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def originalMerge985 : Integer.Sparse OriginalKey := originalMerge977 ++ originalMerge984

theorem reducedMerge985Check : reducedMerge985 = Integer.Sparse.mergeBy masterLess reducedMerge977 reducedMerge984 := by decide +kernel

def reducedMerge986 : Integer.Sparse Master := [(Sum.inr 2556, -762973624782028800000), (Sum.inr 2557, -827530229555527680000), (Sum.inr 2558, 3350500907776081920000), (Sum.inr 2560, -1308617765518049280000), (Sum.inr 2561, -8081533245759160320000), (Sum.inr 2566, 54778388874854400000), (Sum.inr 2569, -54778388874854400000), (Sum.inr 2573, 3475493000755937280000), (Sum.inr 2575, 7730575112285061120000), (Sum.inr 2587, 2089015568665804800000), (Sum.inr 2589, -878316128737689600000), (Sum.inr 2590, 9764819380324270080000), (Sum.inr 2591, -2089015568665804800000), (Sum.inr 2600, 6525212987851407360000), (Sum.inr 2603, 4404201698619555840000), (Sum.inr 2614, 54778388874854400000), (Sum.inr 2617, -9280530725231001600000), (Sum.inr 2618, 34864691456596377600000), (Sum.inr 2620, 10563661873945313280000), (Sum.inr 2631, -15111984861079142400000), (Sum.inr 2632, -6403063116880281600000), (Sum.inr 2633, 15111984861079142400000), (Sum.inr 2635, 3201531558440140800000), (Sum.inr 2641, 7417350658916352000000), (Sum.inr 2643, 7685347844476108800000), (Sum.inr 2652, 4097268088154357760000), (Sum.inr 2653, -2900413559198711808000), (Sum.inr 2654, -59568121389514752000), (Sum.inr 2655, 414737902356922368000), (Sum.inr 2656, 2451504521281536000000)]

def originalMerge986 : Integer.Sparse OriginalKey := originalMerge971 ++ originalMerge985

theorem reducedMerge986Check : reducedMerge986 = Integer.Sparse.mergeBy masterLess reducedMerge971 reducedMerge985 := by decide +kernel

def reducedMerge987 : Integer.Sparse Master := [(Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000)]

def originalMerge987 : Integer.Sparse OriginalKey := originalTerm990 ++ originalTerm991

theorem reducedMerge987Check : reducedMerge987 = Integer.Sparse.mergeBy masterLess reducedTerm990 reducedTerm991 := by decide +kernel

def reducedMerge988 : Integer.Sparse Master := [(Sum.inr 2657, 3659948525761855488000), (Sum.inr 2658, -31848465594580992000), (Sum.inr 2659, -4218827410224709632000)]

def originalMerge988 : Integer.Sparse OriginalKey := originalTerm989 ++ originalMerge987

theorem reducedMerge988Check : reducedMerge988 = Integer.Sparse.mergeBy masterLess reducedTerm989 reducedMerge987 := by decide +kernel

def reducedMerge989 : Integer.Sparse Master := [(Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000)]

def originalMerge989 : Integer.Sparse OriginalKey := originalTerm992 ++ originalTerm993

theorem reducedMerge989Check : reducedMerge989 = Integer.Sparse.mergeBy masterLess reducedTerm992 reducedTerm993 := by decide +kernel

def reducedMerge990 : Integer.Sparse Master := [(Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000)]

def originalMerge990 : Integer.Sparse OriginalKey := originalTerm994 ++ originalTerm995

theorem reducedMerge990Check : reducedMerge990 = Integer.Sparse.mergeBy masterLess reducedTerm994 reducedTerm995 := by decide +kernel

def reducedMerge991 : Integer.Sparse Master := [(Sum.inr 2661, 2542985543602667520000), (Sum.inr 2662, -95323232121126912000), (Sum.inr 2664, 888215115745198080000), (Sum.inr 2669, 1951341470849433600000)]

def originalMerge991 : Integer.Sparse OriginalKey := originalMerge989 ++ originalMerge990

theorem reducedMerge991Check : reducedMerge991 = Integer.Sparse.mergeBy masterLess reducedMerge989 reducedMerge990 := by decide +kernel

end MUB6.Certificate.MixedTargetSemantics

end OAI
